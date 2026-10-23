-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_productOverlapSpectrum
-- name    : QAlgorithms.Papers.Independent.Information100.P21.productOverlapSpectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:48:18.327611+00:00
-- url     : https://prove2.me/theorems/9521d708-26a7-439d-862f-cfd892d05646
-- title:
--   II.4 — Lemma II.4 (Largest product overlap and partial-transpose spectrum). Let |b⟩ be a normalized two-qubit vector with
-- statement:
--   Let $b=\alpha_1u_1\otimes f_1+\alpha_2u_2\otimes f_2$ be a unit two-qubit vector in orthonormal Schmidt bases, with $\alpha_1\ge\alpha_2\ge0$ and $\alpha_1^2+\alpha_2^2=1$. Then
--   $$\max_{p\text{ unit product}}|\langle p|b\rangle|^2=\alpha_1^2,\qquad\operatorname{spec}((|b\rangle\langle b|)^\Gamma)=\{\alpha_1^2,\alpha_2^2,\alpha_1\alpha_2,-\alpha_1\alpha_2\}.$$
--   The maximum is attained and the largest eigenvalue is $\alpha_1^2$. The characteristic-polynomial identity preserves multiplicities, including $\alpha_2=0$.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 7, II.4 — Lemma II.4 (Largest product overlap and partial-transpose spectrum). Let |b⟩ be a normalized two-qubit vector with

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 7, Lemma II.4 (Largest product overlap and partial-transpose spectrum). Let |b⟩ be a normalized two-qubit vector with. -/
theorem productOverlapSpectrum (b : Vec QQ) (hb : ‖b‖=1) (a1 a2 : ℝ)
  (u f : Fin 2 → Vec (Fin 2)) (hs : schmidt b a1 a2 u f) :
  IsGreatest {q : ℝ | ∃ p : Vec QQ, unitProduct p ∧ q=Complex.normSq (inner ℂ p b)} (a1^2) ∧
  (pt (proj b)).charpoly =
    (Polynomial.X-Polynomial.C ((a1^2:ℝ):ℂ)) *
    (Polynomial.X-Polynomial.C ((a2^2:ℝ):ℂ)) *
    (Polynomial.X-Polynomial.C ((a1*a2:ℝ):ℂ)) *
    (Polynomial.X-Polynomial.C ((-a1*a2:ℝ):ℂ)) ∧
  IsGreatest {q : ℝ | ∃ v : QQ → ℂ, v≠0 ∧ (pt (proj b)).mulVec v = (q:ℂ) • v} (a1^2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
