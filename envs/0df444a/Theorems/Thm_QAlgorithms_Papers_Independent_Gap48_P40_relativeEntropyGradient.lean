-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_relativeEntropyGradient
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.relativeEntropyGradient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:16:01.057891+00:00
-- url     : https://prove2.me/theorems/109a48c7-707c-4612-841c-0ad6f5211bcd
-- title:
--   §III, Lemma 1: gradient in the first argument
-- statement:
--   Let $\rho,\sigma$ be positive definite $d\times d$ complex matrices, $d>0$. On the ambient real vector space of Hermitian matrices, let $D(A\|B)=\operatorname{Tr}[A(\log A-\log B)]$. Its gradient in the first argument is characterized by
--
--   $$
--   D(\rho+H\|\sigma)=D(\rho\|\sigma)+\operatorname{Re}\operatorname{Tr}[H(I+\log\rho-\log\sigma)]+o(\|H\|),\qquad H=H^*,\ H\to0.
--   $$
--
--   This describes the ambient gradient, including its identity component; it is not restricted to trace-preserving perturbations.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 2, §III, Lemma 1: gradient in the first argument

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.2, Lemma 1: the ambient Hermitian-cone Frechet gradient is
I+log rho-log sigma. No trace-one tangent restriction is made. The little-o
remainder is an equivalent gradient formulation in finite dimensions. The imported
support-aware entropy is finite in a Hermitian neighborhood of positive definite rho
and sigma, so toReal agrees there with the finite trace expression. -/
theorem relativeEntropyGradient {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : rho.PosDef) (hsigma : sigma.PosDef) :
    (fun D : Mat d => (relativeEntropy (rho + D) sigma).toReal -
      (relativeEntropy rho sigma).toReal -
      (D * (1 + cfc Real.log rho - cfc Real.log sigma)).trace.re)
      =o[nhdsWithin 0 {D : Mat d | D.IsHermitian}] (fun D : Mat d => D) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
