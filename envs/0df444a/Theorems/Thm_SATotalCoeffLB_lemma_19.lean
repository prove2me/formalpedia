-- Prove2me | Theorems.Thm_SATotalCoeffLB_lemma_19
-- name    : SATotalCoeffLB.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:48.831655+00:00
-- url     : https://prove2.me/theorems/62841092-b10b-4799-a7bb-9fd57a78c345
-- title:
--   Lemma 19 — the functional $\tilde L$ on $\mathbb R[X,Y,T]/\langle y^2-1\rangle$
-- statement:
--   Let $E \subseteq \binom{[n]}{2}$ be a set of $m$ pairs of maximum degree at most $8$ with $m \ge 2n$; let $H \in \mathbb F_2^{t\times E}$ be such that every nonzero $z \in C = \ker H$ has weight at least $\delta m$ and every $z \in \mathbb F_2^E$ has $\operatorname{dist}(z, C) \le A \operatorname{wt}(Hz)$ (26), with $A \ge 1$; let $s \in \{\pm1\}^E$; let $0 < \tau < \delta/64$, $\varepsilon = 3\cdot 2^{-\tau n/2}$ (29) and
--
--   $$
--   c := \min\Bigl(\frac{\delta}{6A}, \frac{\tau}{4(A+1)}\Bigr). \tag{32}
--   $$
--
--   Then there is a linear functional $\tilde L$ on $\mathbb R[X, Y, T]/\langle y^2 - 1 : y \in X\cup Y\cup T\rangle$ with the following properties.
--
--   1. $\tilde L(1) = 1$.
--   2. $\tilde L(D q_e) = 0$ for every $e \in E$ and every polynomial $D$.
--   3. For every pair $e \in \binom{[n]}{2}$ and every polynomial $C$, $|\tilde L(C p_e)| \le \frac{\varepsilon}{2} \|C\|_1$.
--   4. For every $k \le cn$, $\tilde L$ is nonnegative on every nonnegative $k$-junta in $X, Y, T$.
--
--   Applied to the identity (25), these four properties give the lower bound of Theorem 3.
--
--   Differences from the source:
--   - generalization: the data of Section 9 for sufficiently large $m$: $n = \lceil m/4\rceil$, the degree-8 graph, the code and matrix of Lemma 15 → any $E$ of maximum degree $\le 8$ with $m = |E| \ge 2n$ and any $H$ whose kernel has minimum distance $\ge \delta m$ and satisfies (26) with $A \ge 1$; reason: the page's proof uses exactly these facts (via Lemmas 16 and 17 and $m \ge 2n$); Lemma 15's rate, row count and column weights are not used
--   - encoding: $k \le cn$ → a natural number $k$ with $k \le cn$ in $\mathbb R$; reason: $k$ counts variables
--   - encoding: a linear functional on $\mathbb R[X,Y,T]/\langle y^2-1\rangle$; $\|C\|_1$ → an $\mathbb R$-linear map on functions on the cube of $X\sqcup Y\sqcup T$; `coeffNorm`; reason: the ring model of `CubeFn`
--   - encoding: signs $s_e \in \{\pm 1\}$ → real numbers with $s_e = 1 \lor s_e = -1$; reason: same values
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Lemma 19, p.54 (with Eq. (32), p.54, and Eq. (29), p.52)

import Mathlib
import Definitions.Def_SATotalCoeffLB_andCheck
import Definitions.Def_SATotalCoeffLB_parityCheckH
import Definitions.Def_SATotalCoeffLB_coeffNorm
import Definitions.Def_SATotalCoeffLB_DependsOnAtMost

namespace SATotalCoeffLB

/-- **Lemma 19 (the functional `L̃`)**, p.54 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

Standing data of Section 9: a set `E` of `m` pairs on `[n]` with maximum degree at most eight and
`m ≥ 2n`; a matrix `H ∈ F₂^{t×E}` whose code `C = ker H` has minimum distance at least `δm` and
satisfies Eq. (26), `dist(z, C) ≤ A·wt(Hz)` with `A ≥ 1`; signs `s ∈ {±1}^E`; `0 < τ < δ/64`;
`ε := 3·2^{−τn/2}` (Eq. (29)) and `c := min(δ/(6A), τ/(4(A + 1)))` (Eq. (32)). Then there is a
linear functional `L̃` on `ℝ[X, Y, T]/⟨y² − 1 : y ∈ X ∪ Y ∪ T⟩` such that
1. `L̃(1) = 1`;
2. `L̃(D q_e) = 0` for every `e ∈ E` and every polynomial `D`;
3. `|L̃(C p_e)| ≤ (ε/2)‖C‖₁` for every pair `e` and every polynomial `C`;
4. for every `k ≤ cn`, `L̃` is nonnegative on every nonnegative `k`-junta in `X, Y, T`.

**Formalization Note** "For all sufficiently large `m`" (with `n = ⌈m/4⌉`) enters the page's proof
only through `m ≥ 2n` (Lemma 16 and Property 4); the statement assumes `m ≥ 2n`. `k` is a natural
number. -/
theorem lemma_19 (n t : ℕ) (E : Finset (Pair n)) (H : Matrix (Fin t) E (ZMod 2))
    (s : E → ℝ) (hs : ∀ e, s e = 1 ∨ s e = -1) (δ A τ : ℝ) (hA : 1 ≤ A)
    (hτ : 0 < τ) (hτδ : τ < δ / 64)
    (hdeg : ∀ v : Fin n, (E.filter fun e => e.1.1 = v ∨ e.1.2 = v).card ≤ 8) (hm : 2 * n ≤ E.card)
    (hdist : ∀ z : E → ZMod 2, H.mulVec z = 0 → z ≠ 0 → δ * E.card ≤ (hammingNorm z : ℝ))
    (h26 : ∀ z : E → ZMod 2, ∃ c : E → ZMod 2, H.mulVec c = 0 ∧
      (hammingNorm (z + c) : ℝ) ≤ A * (hammingNorm (H.mulVec z) : ℝ)) :
    ∃ Lt : CubeFn (Var n t) →ₗ[ℝ] ℝ,
      Lt 1 = 1 ∧
      (∀ (e : E) (D : CubeFn (Var n t)), Lt (D * parityCheckH H s e) = 0) ∧
      (∀ (e : Pair n) (Cf : CubeFn (Var n t)),
        |Lt (Cf * andCheck t e)| ≤ 3 * (2 : ℝ) ^ (-(τ * n / 2)) / 2 * coeffNorm Cf) ∧
      ∀ k : ℕ, (k : ℝ) ≤ min (δ / (6 * A)) (τ / (4 * (A + 1))) * n →
        ∀ h : CubeFn (Var n t), DependsOnAtMost k h → (∀ x, 0 ≤ h x) → 0 ≤ Lt h := by sorry

end SATotalCoeffLB
