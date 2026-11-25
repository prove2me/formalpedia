-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordRing_eq_cd809ea45753
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coordRing_eq_cd809ea45753
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:57.907796+00:00
-- url     : https://prove2.me/theorems/22d820c3-9865-41f6-99da-4d10258b4290
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coord Ring eq cd809ea45753: P2 M Ground Theory Heights  Heights Kleiman coord Ring eq cd809ea45753
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coord Ring eq cd809ea45753 construction uses the P2 M Ground Theory Heights  Heights Kleiman coord Ring eq cd809ea45753 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L397-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L397-L397

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coordRing_eq_cd809ea45753 : coordRing (S := S) x = (cone (S := S) x).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coordRing_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_coordRing_eq_cd809ea45753
