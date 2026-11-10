-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_theorem_5_4
-- name    : TurnstileRank.TightBounds.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:10:15.095373+00:00
-- url     : https://prove2.me/theorems/1b255775-7865-4f2b-b49c-eef9a7189627
-- title:
--   Theorem 5.4 — packed lower bound: s ≥ qrB
-- statement:
--   Theorem 5.4 (Packed lower bound). Let A be a linear sketch of s bits with public randomness ρ. Suppose that for every cell c = (j, a) and every input Z independent of cell c and ρ, of mass less than (2r − 1)tw_j, at most θtw_j of it in the position of c, and with a fixed mass before that position, the state M of A on V_c + Z satisfies I(V_c ; M | ρ) ≥ B. Then s ≥ qrB.
--
--   Packed input (p. 26): integers $q\ge1$, $1\le h\le q$, $r,t,b\ge1$; disjoint groups $P_0<\dots<P_{h-1}$ of consecutive coordinates, each $r$ consecutive blocks (positions) of $b$ coordinates; cell $(j,a)$, $0\le j<q$, $1\le a\le r$, is a tuple $V_{j,a}$ of $t$ items in position $a$ of $P_{j\bmod h}$, each with weight $w_j=2^{q-1-j}$; $\theta=2^{1-h}$ if $h<q$ and $\theta=0$ if $h=q$.
--
--   In Lean: the group $P_g$ starts at `off g` ($g<h$), with `off g + rb ≤ off g'` for $g<g'<h$ and `off g + rb ≤ U`; position $a$ ($0$-based) of $P_g$ is $[\mathrm{off}\,g+ab,\ \mathrm{off}\,g+ab+b)$. Each cell $(j,a)$ has an arbitrary law `cellLaw j a` on $t$-tuples of offsets in its position. If $L$ has `HasSpace L s` and, for every cell $(j,a)$ and every random input $Z$ independent of the cell and of $\rho$ with $\|Z\|_1<(2r-1)tw_j$, mass at most $\theta tw_j$ in the cell's position and a fixed mass before that position, $I(V_{j,a};A_\rho(V_{j,a}+Z)\mid\rho)\ge B$, then $s\ge qrB$.
--
--   Differences from the source:
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: Z an input (a nonnegative frequency vector) independent of V and ρ, with bounds on its masses → Z has an arbitrary discrete law ζ on ℕ^U, independent of the seed and the instance (`blockInfo`), and every bound holds for every z in the support of ζ; reason: an input is a nonnegative integer vector; a bound on a random input holds almost surely, i.e. on the support
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
--   - encoding: groups P_0 < … < P_{h−1} of consecutive coordinates, positions 1, …, r, cells (j, a) with 1 ≤ a ≤ r → groups given by start offsets `off g` with the disjointness and fit conditions; positions and the cell index a are 0-based (`Fin r`); items of a cell are offsets `Fin b` inside its position; reason: every admissible choice of groups is covered; a bijective reindexing
--   - encoding: independent random cells with fixed sizes and weights ("the construction uses nothing about the cells except that they are independent and have fixed sizes and weights") → an arbitrary law `cellLaw j a` for each cell; reason: the hypothesis and conclusion concern one cell at a time; the cells' joint law is the product of these laws
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Theorem 5.4, printed p. 26 (PDF 27)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Blocks

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Theorem 5.4 (Packed lower bound). The groups `P_0 < ⋯ < P_{h−1}` start at `off 0 < ⋯ < off (h−1)`;
cell `(j, a)` (`j < q`, `a < r`) is a tuple of `t` items with law `cellLaw j a` in position `a` of
`P_{j mod h}`, i.e. on the block `[pos, pos + b)` with `pos = off (j mod h) + a b`, with weight
`w_j = 2^{q−1−j}`. -/
theorem theorem_5_4 (U q h r t b : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h) (hhq : h ≤ q) (hr : 1 ≤ r)
    (ht : 1 ≤ t) (hb : 1 ≤ b) (off : ℕ → ℕ)
    (hoff : ∀ g g' : ℕ, g < g' → g' < h → off g + r * b ≤ off g')
    (hfit : ∀ g : ℕ, g < h → off g + r * b ≤ U)
    (cellLaw : Fin q → Fin r → PMF (Fin t → Fin b))
    {Ρ G Q O : Type} [AddCommGroup G] (L : LinearSketch U Ρ G Q O) (s B : ℝ)
    (hs : L.HasSpace s)
    (hcell : ∀ (j : Fin q) (a : Fin r) (ζ : PMF (Fin U → ℕ)),
      (∀ z ∈ ζ.support,
        (totalMass z : ℝ) < (2 * r - 1) * t * layerWeight q j ∧
        (massIn z (off (j.val % h) + a.val * b) (off (j.val % h) + a.val * b + b) : ℝ) ≤
          theta h q * t * layerWeight q j) →
      (∃ m0 : ℕ, ∀ z ∈ ζ.support, massIn z 0 (off (j.val % h) + a.val * b) = m0) →
      ENNReal.ofReal B ≤
        blockInfo L (cellLaw j a) ζ id
          (fun v => placeVec U (fun i => off (j.val % h) + a.val * b + (v i : ℕ))
            (layerWeight q j))) :
    (q : ℝ) * r * B ≤ s := by sorry

end TurnstileRank.TightBounds
