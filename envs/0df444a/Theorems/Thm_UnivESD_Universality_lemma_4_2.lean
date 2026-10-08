-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_4_2
-- name    : UnivESD.Universality.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:46.98488+00:00
-- url     : https://prove2.me/theorems/7321c894-a3e1-49a7-b3b7-2e32d7df535a
-- title:
--   Lemma 4.2 (high-dimensional contribution): $\frac1n\sum_{(1-\delta)n\le i\le n-n^{0.99}}|\log\mathrm{dist}(\frac1{\sqrt n}X_i,V_i)|=O(\varepsilon)$
-- statement:
--   Work in the setting of §4 (after the shift $z=0$): $x$ has zero mean and unit variance, $M_n$ satisfies (1.3), $A_n=M_n+X_n$, and the rows $Z_i$ of $M_n$ satisfy
--   $$\|Z_i\|=O(\sqrt n)\qquad\text{for all }n/2\le i\le n\quad(4.2).$$
--   Let $X_1,\dots,X_n$ be the rows of $A_n$ and $V_i=\mathrm{span}(X_1,\dots,X_{i-1})$. Then for every $\varepsilon>0$ there exists $0<\delta<1/2$ such that, with probability $1$,
--   $$\frac1n\sum_{(1-\delta)n\le i\le n-n^{0.99}}\Bigl|\log\mathrm{dist}\Bigl(\frac1{\sqrt n}X_i,V_i\Bigr)\Bigr|=O(\varepsilon)$$
--   for all but finitely many $n$. A similar result holds with $\mathrm{dist}(\frac1{\sqrt n}X_i,V_i)$ replaced by $\mathrm{dist}(\frac1{\sqrt n}Y_i,W_i)$ for the rows of $B_n$.
--
--   By (2.3) the normalized log-determinant is $\frac1n\sum_i\log\mathrm{dist}(\frac1{\sqrt n}X_i,V_i)$; this lemma shows the rows between $(1-\delta)n$ and $n-n^{0.99}$ contribute little.
--
--   **Formalization Note.** $O(\varepsilon)$ is $C\varepsilon$ with $C$ fixed before $\varepsilon$. Since Lean's $\log 0=0$ would make a vanishing distance contribute nothing, the conclusion also asserts that every distance in the range is positive. The paper obtains (4.2) "by permuting the rows"; it is a hypothesis here, with an explicit constant $K$. Indices are one-based in the inequalities. The $B_n$ version is the same statement applied to the array of $y$'s and is not posed separately. The matrices for different $n$ come from one i.i.d. array.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2045 (PDF 23), Lemma 4.2; setting p. 2043–2044 (PDF 21–22), (4.2)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 4.2 (high-dimensional contribution), p. 2045, in the setting of §4 (`z = 0`, (1.3),
and the row normalization (4.2)). Rows are one-based: zero-based row `i` is the paper's
`X_{i+1}`. -/
theorem lemma_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hx : IsIIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : ShiftBound M)
    (h42 : ∃ K : ℝ, ∀ n (i : Fin n), (n : ℝ) ≤ 2 * ((i : ℕ) + 1 : ℝ) →
      ‖row (M n) i‖ ≤ K * Real.sqrt n) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      (∀ i : Fin n, (1 - δ) * n ≤ ((i : ℕ) + 1 : ℝ) → ((i : ℕ) + 1 : ℝ) ≤ n - (n : ℝ) ^ (0.99 : ℝ) →
        0 < rowDist (invSqrt n • (M n + cornerMatrix xs n ω)) i) ∧
      (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.filter (fun i : Fin n =>
          (1 - δ) * n ≤ ((i : ℕ) + 1 : ℝ) ∧ ((i : ℕ) + 1 : ℝ) ≤ n - (n : ℝ) ^ (0.99 : ℝ)),
        |Real.log (rowDist (invSqrt n • (M n + cornerMatrix xs n ω)) i)| ≤ C * ε := by sorry

end UnivESD.Universality
