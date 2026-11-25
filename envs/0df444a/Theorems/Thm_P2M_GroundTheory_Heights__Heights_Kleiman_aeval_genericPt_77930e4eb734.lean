-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_genericPt_77930e4eb734
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_aeval_genericPt_77930e4eb734
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:18.481808+00:00
-- url     : https://prove2.me/theorems/517a3915-7c8c-4b06-be92-512cf8b09a7f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman aeval generic Pt 77930e4eb734: P2 M Ground Theory Heights  Heights Kleiman aeval generic Pt 77930e4eb734
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman aeval generic Pt 77930e4eb734 construction uses the P2 M Ground Theory Heights  Heights Kleiman aeval generic Pt 77930e4eb734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L953-L960
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L953-L960

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (k : Type u) [Field k] (N : ℕ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_aeval_genericPt_77930e4eb734 (f : Poly k N) :
    aeval (genericPt k N) f = algebraMap (Poly k N) (FractionRing (Poly k N)) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«aeval_genericPt» := P2M_GroundTheory_Heights__Heights_Kleiman_aeval_genericPt_77930e4eb734
