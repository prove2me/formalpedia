-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_entanglementFamilies
-- name    : QAlgorithms.Papers.Independent.Information100.P69.entanglementFamilies
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:06:10.340537+00:00
-- url     : https://prove2.me/theorems/4e82d5e7-0432-42c2-9358-bca7c043b553
-- title:
--   Entanglement-breaking and PPT alternatives
-- statement:
--   The full EB and PPT block-channel families satisfy F1–F5 for any faithful input and output witnesses. EB means separable Choi operator across the entire input-reference/output cut; PPT means its partial transpose on the entire output is positive. For every isometry $J:A\to B$, target $\mathcal N=\operatorname{Ad}_J$, $n\ge1$, and $0<\varepsilon<1$, both families have
--   $$E_n=n\log_2 a,\qquad\beta_{\varepsilon,n}=(1-\varepsilon)a^{-n},\qquad a=\dim A.$$
--   These are exact finite-block entropy and testing benchmarks, including $a=1$.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 23, Proposition 22

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 22, whole-block EB and PPT and exact isometric testing/entropy, PDF p.23. -/
theorem entanglementFamilies [Nonempty A] [Nonempty B] (tau : Matrix A A ℂ) (omega : Matrix B B ℂ)
    (htau : Faithful tau) (homega : Faithful omega) :
    ∀ F ∈ ({ebFamily, pptFamily} : Set (BlockFamily A B)),
      Admissible F omega ∧ Additional F tau ∧
      ∀ J : Matrix B A ℂ, J.conjTranspose*J = 1 →
        (∀ n, 1 ≤ n → resourceEntropy (power (conjSuperop J) n) (F n) =
          ENNReal.ofReal ((n:ℝ)*Real.logb 2 (Fintype.card A))) ∧
        (∀ n, 1 ≤ n → ∀ eps : ℝ, 0 < eps → eps < 1 →
          beta (power (conjSuperop J) n) (F n) eps = (1-eps)*(Fintype.card A:ℝ)^(-(n:ℤ))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
