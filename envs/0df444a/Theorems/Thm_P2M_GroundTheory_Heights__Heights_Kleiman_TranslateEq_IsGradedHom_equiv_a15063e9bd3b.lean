-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:35.03084+00:00
-- url     : https://prove2.me/theorems/e4585449-0950-44ee-a9d5-78c90a7291a8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq Is Graded Hom equiv a15063e9bd3b: P2 M Ground Theory Heights  Heights Kleiman Translate Eq Is Graded Hom equiv a15063e9bd3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq Is Graded Hom equiv a15063e9bd3b construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq Is Graded Hom equiv a15063e9bd3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L68-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] (N : ℕ)
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b {M' : Type} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
    [IsScalarTower S (Poly S N) M'] (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
    (f : M →ₗ[Poly S N] M') :
    IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f ↔
      ∃ g : Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G'), g.toLin = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«IsGradedHom».«equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
