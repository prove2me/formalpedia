-- Prove2me | Theorems.Thm_UnderstandingML_chaining_corollary
-- name    : UnderstandingML.chaining_corollary
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:50:30.909774+00:00
-- url     : https://prove2.me/theorems/fe455b87-0624-480a-8191-ca02d1192b31
-- title:
--   Lemma 27.5: if √(log N(c2^{−k}, A)) ≤ α + βk for all k ≥ 1, then R(A) ≤ (6c/m)(α + 2β)
-- statement:
--   **Lemma 27.5.** Assume that there are $\alpha, \beta > 0$ such that for any $k \ge 1$ we have $\sqrt{\log(N(c\,2^{-k}, A))} \le \alpha + \beta k$. Then $R(A) \le \frac{6c}{m}(\alpha + 2\beta)$.
--
--   Formally: with $c$ an enclosing radius of $A$ as in Lemma 27.4.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.2 p. 390, Lemma 27.5 with its proof

import Definitions.Def_UnderstandingML_Covering

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 27.5** (p. 390). Assume that there are `α, β > 0` such that for any `k ≥ 1` we have
`√(log N(c 2^{−k}, A)) ≤ α + βk`. Then `R(A) ≤ (6c/m)(α + 2β)`. Hypotheses on `c` as in
Lemma 27.4. -/
theorem chaining_corollary {m : ℕ} (hm : 0 < m) (A : Set (Fin m → ℝ)) (hA : A.Nonempty) (c : ℝ)
    (abar : Fin m → ℝ) (hc : ∀ a ∈ A, eucNorm (a - abar) ≤ c) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β)
    (hN : ∀ k : ℕ, 1 ≤ k →
      Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat)) ≤ α + β * k) :
    rademacher A ≤ 6 * c / m * (α + 2 * β) := by sorry

end UnderstandingML
