-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_finiteBlockSmoothing
-- name    : QAlgorithms.Papers.Independent.Information100.P69.finiteBlockSmoothing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:02:51.006576+00:00
-- url     : https://prove2.me/theorems/80fc109b-3edc-4825-b66d-4949574d07ab
-- title:
--   Finite-block smoothing bounds
-- statement:
--   For admissible alternatives, every $n\ge1$, $0<\varepsilon<1$, and $0\le\delta<2(1-\varepsilon)$ obey
--   $$a_{\varepsilon,n}+\log_2(1-\varepsilon-\delta/2)\le Z_n^\delta,$$
--   where $a_{\varepsilon,n}=-\log_2\beta_{\varepsilon,n}$. If F4–F5 also hold, then for $0<\delta\le1/16$ and $\varepsilon+\delta/2<1$,
--   $$Z_n^\delta\le a_{\varepsilon,n}+K_\varepsilon n^{2/3}\log_2((n+1)/\delta).$$
--   The upper-bound constant has the dimension, witness-eigenvalue, and tolerance dependence of Theorem 16. This records both the joint smoothing estimate and the wider-domain, weaker-assumption lower bound.
--
--   Here $Z_n^\delta$ is the minimum logarithmic CP-domination cost over CPTP approximations within diamond radius $\delta$ and over all free dominators at blocklength $n$.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 20, Corollary 17

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Corollary 17, including the weaker-assumption lower bound at delta=0, PDF p.20. -/
theorem finiteBlockSmoothing [Nonempty A] [Nonempty B] :
    (∀ (N : Superop A B), IsChannel N → ∀ F : BlockFamily A B,
      ∀ omega : Matrix B B ℂ, Admissible F omega →
      ∀ n, 1 ≤ n → ∀ eps delta : ℝ, 0 < eps → eps < 1 → 0 ≤ delta → delta < 2*(1-eps) →
        ENNReal.ofReal (exponent (power N n) (F n) eps+Real.logb 2 (1-eps-delta/2)) ≤
          smoothCost (power N n) (F n) delta) ∧
    (∀ t w eps : ℝ, 0 < t → 0 < w → 0 < eps → eps < 1 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ tau : Matrix A A ℂ, ∀ omega : Matrix B B ℂ,
      minPositiveEigenvalue tau = t → minPositiveEigenvalue omega = w →
      ∀ F : BlockFamily A B, Admissible F omega → Additional F tau →
      ∀ N : Superop A B, IsChannel N → ∀ n, 1 ≤ n →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/16 → eps+delta/2 < 1 →
        smoothCost (power N n) (F n) delta ≤ ENNReal.ofReal
          (exponent (power N n) (F n) eps+overhead K n delta)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
