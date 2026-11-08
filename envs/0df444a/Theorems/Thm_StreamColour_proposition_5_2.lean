-- Prove2me | Theorems.Thm_StreamColour_proposition_5_2
-- name    : StreamColour.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:09.460379+00:00
-- url     : https://prove2.me/theorems/98cc1f5c-b12b-4130-8549-cb5f52bac188
-- title:
--   Proposition 5.2 — one-pass almost-clique decomposition in $\tilde O(n)$ bits (corrected: for $\Delta\ge\Delta_0(\varepsilon)$)
-- statement:
--   There are absolute constants $\eta,\varepsilon_0>0$ such that for every fixed $0<\varepsilon<\varepsilon_0$ there is $\Delta_0$ with the following property. For every fixed $c>0$ there is a randomized one-pass streaming program that, for every $n$-vertex graph $G$ of maximum degree at most $\Delta$, with $\Delta_0\le\Delta\le n-1$, and every order of its edges, uses at most $A\,n\,\ell^B$ bits on every execution and, with probability at least $1-n^{-c}$, outputs a partition satisfying Definition 5.1.
--
--   The paper cites this from Flin and Halldórsson; it is the structural input of Algorithm B. No colourability is assumed.
--
--   Differences from the source:
--   - correction: no lower bound on $\Delta$ → $\Delta\ge\Delta_0(\varepsilon)$; reason: as printed the statement is false: for $\varepsilon<1$, $G=K_2$ and $\Delta=1=n-1$, each vertex has $\zeta=0<\eta\varepsilon^2\Delta$, so $S_0$ is empty, a piece has size in $[1-\varepsilon/2,1+\varepsilon/2]$, so it is a singleton, and then $e_C(v)=1>\varepsilon\Delta$, so no decomposition exists; likewise $K_{\Delta+1}$ for all $\Delta<1/\varepsilon$, so the threshold must depend on $\varepsilon$; §5 uses the proposition only with $\Delta>C_*h^2$ and $C_*$ chosen after $\varepsilon$
--   - reading: "a randomized algorithm", with no machine named → a `DynBrooks.Program` (finite instruction list, memory $\mathbb N\to\{0,1\}^w$, read-once input, write-only output, coin words) of word size $w=c_w\ell(n)$, fixed before $n$; reason: a finite-state model with an arbitrary output map would make the workspace clause empty, and every step of the paper's pseudo-code runs here
--   - encoding: $\tilde O(n)$ bits on every execution, including postprocessing workspace → $A\,n\,\ell(n)^B$ bits, as `w * written.card`, for all $\omega,t$, with $P,c_w,A,B$ after $\varepsilon,c$ and before $n,\Delta,G$; reason: $\tilde O$ suppresses factors polynomial in $\log(n+1)$ (§3, p.20); cells ever written are the workspace, for all coin tapes and all times, including runs that never halt; output words are write-only and not charged
--   - encoding: "with high probability" → $1-n^{-c}$ for each prescribed $c>0$, a program for each $c$; reason: the convention of §3, p.20
--   - encoding: "computes a partition" → the program halts with a list of length $n$, naming each vertex's piece, $0$ for $S_0$; the input is $[n,\Delta]$, the edge labels and the sentinel $0$; reason: the paper leaves the format open
--   - encoding: "with probability at least $c$" → a measurable event of measure at least $c$ inside the success set, under independent uniform coin words; reason: the inner bound avoids overstating an event by outer measure; uniform samples come by rejection sampling, exact almost surely
--   - generalization: the input graph of §5 (promised $(\Delta-k)$-colourable, with $1\le k<\Delta$) → any graph of maximum degree at most $\Delta$ with $1\le\Delta$, and no $k$ in the input; reason: the decomposition uses neither the promise nor $k$ (§5, p.49: it "does not itself require $\Delta>C_*h^2$"); the paper's graphs are a special case
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Proposition 5.2, p.50 (PDF 52); Definition 5.1, pp.49–50

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_StreamModel
import Definitions.Def_StreamColour_ACD

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Proposition 5.2, p.50 (PDF 52), corrected.

**Correction.** As printed there is no lower bound on `∆`, and the statement is false: a graph may have no
decomposition at all. For `ε < 1` and `G = K₂` with `∆ = 1 = n − 1`, each vertex has `ζ = 0 < η ε² ∆`, so `S₀` is empty; a piece
has size in `[1 − ε/2, 1 + ε/2]`, so it is a singleton, and then `e_C(v) = 1 > ε ∆`. The same happens for `K_{∆+1}` for every
`∆ < 1/ε`, so the threshold must grow with `1/ε`. The minimal correction adds `∆ ≥ ∆₀(ε)`. §5 uses the proposition only with
`∆ > C_∗h²` and `C_∗` chosen after `ε`, so nothing downstream changes.

**Formalization Note.** "High probability" is `∀ c > 0` (p.20). `Õ(n)` is `A n ℓ(n)^B`, on every `ω` and `t`, with `P, cw, A, B` after `ε, c`
and before `n, ∆, G`. No colourability promise and no relation to `h` is present. The input is `[n, ∆]`, the edge labels and the
sentinel; the output has length `n` and names each vertex's piece, `0` for `S₀`. The result is cited from [FH26b, Proposition 3.5] and
not proved in the paper. -/
theorem proposition_5_2 : ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ Δ₀ : ℕ,
    ∀ c : ℝ, 0 < c → ∃ (P : DynBrooks.Program) (cw A B : ℕ),
    ∀ (n Δ : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
    Δ₀ ≤ Δ → 1 ≤ Δ → Δ ≤ n - 1 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → IsEdgeStream G es →
    let w := cw * ell n
    let c₀ := initConfig w ([n, Δ] ++ edgeWords es ++ [0])
    (∀ (ω : ℕ → BitVec w) (t : ℕ),
      spaceBits w (DynBrooks.run P ω c₀ t) ≤ A * n * ell n ^ B) ∧
    ProbAtLeast (DynBrooks.coinMeasure w)
      {ω | ∃ t, P[(DynBrooks.run P ω c₀ t).pc]? = some DynBrooks.Instr.halt ∧
        (DynBrooks.run P ω c₀ t).output.length = n ∧
        IsACD η ε Δ G fun v => (DynBrooks.run P ω c₀ t).output.getD v.val 0}
      (ENNReal.ofReal (1 - (n : ℝ) ^ (-c))) := by sorry

end StreamColour
