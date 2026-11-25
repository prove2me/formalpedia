-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_homR_215a0de6330c
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_homR_215a0de6330c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:21.204102+00:00
-- url     : https://prove2.me/theorems/3d54ac28-3513-426e-af40-47184b3c6efd
-- title:
--   P2 M Ground Theory Heights  Heights Vertical chart Psi comp hom R 215a0de6330c: P2 M Ground Theory Heights  Heights Vertical chart Psi comp hom R 215a0de6330c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical chart Psi comp hom R 215a0de6330c construction uses the P2 M Ground Theory Heights  Heights Vertical chart Psi comp hom R 215a0de6330c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L263-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L263-L268

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {D : Type*} [CommRing D] {n : ℕ}
variable (e : ℕ) (R : Type*) [CommRing R] [Algebra (MvPolynomial (Par e n) D) R]
variable (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D))

theorem P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_homR_215a0de6330c [IsLocalization S R] :
    (chartPsi e R Q j S).comp (chartHomR e R Q j S) =
      (algebraMap _ (ChartBj e R Q j)).comp (algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«chartPsi_comp_homR» := P2M_GroundTheory_Heights__Heights_Vertical_chartPsi_comp_homR_215a0de6330c
