-- Prove2me | Theorems.Thm_RobustPoA_Tight_lemma_5_3
-- name    : RobustPoA.Tight.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:30.108783+00:00
-- url     : https://prove2.me/theorems/de85448d-08a9-4730-b089-64110f13242b
-- title:
--   Lemma 5.3, p. 25 — two tight constraints at an attained optimum
-- statement:
--   Let $\mathcal C$ be a nonempty finite set of strictly positive, nondecreasing cost functions, let $n\ge1$, and suppose $(\widehat\lambda,\widehat\mu)\in\mathcal A(\mathcal C,n)$ attains $\gamma(\mathcal C,n)$. Then there are functions $c_1,c_2\in\mathcal C$, loads $x_1,x_2\in\{0,\ldots,n\}$, positive reference loads $x_1^*,x_2^*\in\{1,\ldots,n\}$, and $\eta\in[0,1]$ such that, for $j=1,2$,
--
--   $$c_j(x_j+1)x_j^*=\widehat\lambda c_j(x_j^*)x_j^*+\widehat\mu c_j(x_j)x_j,$$
--
--   and
--
--   $$\eta c_1(x_1+1)x_1^*+(1-\eta)c_2(x_2+1)x_2^*=\eta c_1(x_1)x_1+(1-\eta)c_2(x_2)x_2.$$
--
--   These two active constraints describe the finite parameter optimum used by the lower-bound construction.
--
--   **Formalization Note** Nonemptiness is the standing assumption stated at the start of §5.1. Without it, the existence of $c_1,c_2$ would be false. Attainment is equality in $[0,\infty]$; strict positivity ensures the encoded ratio is the real ratio.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Lemma 5.3, p. 25, equations (42)–(43)

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal

/-- Lemma 5.3, p. 25: an attained optimum of the finite smoothness problem has two
tight resource constraints whose convex mixture balances current and deviation costs. -/
theorem lemma_5_3 (C : Set (ℕ → ℝ)) (hfinite : C.Finite) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c) (n : ℕ) (hn : 1 ≤ n)
    (p : ℝ × ℝ) (hp : p ∈ smoothParamsN C n)
    (hattain : ENNReal.ofReal (p.1 / (1 - p.2)) = gammaN C n) :
    ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ x₁ x₂ x₁' x₂' : ℕ, ∃ η : ℝ,
      x₁ ≤ n ∧ x₂ ≤ n ∧
      1 ≤ x₁' ∧ x₁' ≤ n ∧ 1 ≤ x₂' ∧ x₂' ≤ n ∧
      0 ≤ η ∧ η ≤ 1 ∧
      c₁ (x₁ + 1) * (x₁' : ℝ) =
        p.1 * (c₁ x₁' * (x₁' : ℝ)) + p.2 * (c₁ x₁ * (x₁ : ℝ)) ∧
      c₂ (x₂ + 1) * (x₂' : ℝ) =
        p.1 * (c₂ x₂' * (x₂' : ℝ)) + p.2 * (c₂ x₂ * (x₂ : ℝ)) ∧
      η * (c₁ (x₁ + 1) * (x₁' : ℝ)) +
        (1 - η) * (c₂ (x₂ + 1) * (x₂' : ℝ)) =
          η * (c₁ x₁ * (x₁ : ℝ)) + (1 - η) * (c₂ x₂ * (x₂ : ℝ)) := by sorry

end RobustPoA.Tight
