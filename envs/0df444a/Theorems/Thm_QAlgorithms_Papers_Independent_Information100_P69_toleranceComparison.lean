-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_toleranceComparison
-- name    : QAlgorithms.Papers.Independent.Information100.P69.toleranceComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:03:21.011831+00:00
-- url     : https://prove2.me/theorems/fb25cf5b-5d4c-4aef-99fc-eab482bbbaa6
-- title:
--   Comparison of testing tolerances
-- statement:
--   Assume F1–F5. For every $0<\varepsilon_-\le\varepsilon_+<1$, some finite $K\ge0$ works simultaneously for all $n\ge1$ and both tolerances $\varepsilon,\varepsilon'\in[\varepsilon_-,\varepsilon_+]$:
--   $$|a_{\varepsilon,n}-a_{\varepsilon',n}|\le Kn^{2/3}\log_2(n+1).$$
--   For any two fixed tolerances in $(0,1)$, $(a_{\varepsilon,n}-a_{\varepsilon',n})/n\to0$. Pointwise interval bounds express the source's supremum without introducing an unguarded real supremum. This quantifies tolerance independence.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 20, Lemma 18

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 18, uniform interval comparison and normalized difference limit, PDF p.20. -/
theorem toleranceComparison [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (tau : Matrix A A ℂ) (omega : Matrix B B ℂ) (hF : Admissible F omega) (hextra : Additional F tau) :
    (∀ lo hi : ℝ, 0 < lo → lo ≤ hi → hi < 1 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ n, 1 ≤ n → ∀ eps eps' : ℝ, eps ∈ Set.Icc lo hi → eps' ∈ Set.Icc lo hi →
        |exponent (power N n) (F n) eps-exponent (power N n) (F n) eps'| ≤
          K*(n:ℝ)^(2/3:ℝ)*Real.logb 2 ((n:ℝ)+1)) ∧
    ∀ eps eps' : ℝ, 0 < eps → eps < 1 → 0 < eps' → eps' < 1 →
      Tendsto (fun j : ℕ => (exponent (power N (j+1)) (F (j+1)) eps-
        exponent (power N (j+1)) (F (j+1)) eps')/(j+1)) atTop (nhds 0) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
