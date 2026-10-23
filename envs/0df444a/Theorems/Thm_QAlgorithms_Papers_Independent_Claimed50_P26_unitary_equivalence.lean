-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_unitary_equivalence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.unitary_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:11:23.153954+00:00
-- url     : https://prove2.me/theorems/f4ab9d77-84b3-429a-9e25-e648e60c450d
-- title:
--   Unnumbered invariance under fixed input/output unitary conjugations
-- statement:
--   Let $\Phi:\mathcal B(\mathbb C^2)\to\mathcal B(\mathbb C^2)$ be a unital qubit channel, so $\Phi(I/2)=I/2$, and let $\alpha>1$. Fix input and output unitaries $U,V$ and define $\Psi(X)=V\Phi(UXU^\dagger)V^\dagger$ on every operator. Then the regularized ensemble Rényi–Holevo quantity obeys
--
--   $$
--   \bar\chi_\alpha^*(\Psi)=\bar\chi_\alpha^*(\Phi).
--   $$
--
--   The conjugations are fixed independently of the message and block input. This is the invariance observation used in the source's reduction of unital qubit channels to Pauli diagonal form.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 5, Unnumbered invariance under fixed input/output unitary conjugations

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.5, unital qubit channels: regularized alpha-Holevo invariance
under fixed input/output conjugations, with unitaries independent of the message.
The source's opening scope is retained even though a more general invariant is true. -/
theorem unitary_equivalence
    (Phi : Superop (Fin 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hunit : Phi ((2 : ℂ)⁻¹ • 1) = (2 : ℂ)⁻¹ • 1)
    (alpha : ℝ) (ha : 1 < alpha)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    regularizedChi alpha (fun X =>
      (V : Matrix (Fin 2) (Fin 2) ℂ)*Phi ((U : Matrix (Fin 2) (Fin 2) ℂ)*X*
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)*(V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) =
      regularizedChi alpha Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
