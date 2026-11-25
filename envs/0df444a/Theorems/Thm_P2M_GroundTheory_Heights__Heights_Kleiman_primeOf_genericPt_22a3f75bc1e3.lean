-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_genericPt_22a3f75bc1e3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_genericPt_22a3f75bc1e3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:38.059808+00:00
-- url     : https://prove2.me/theorems/700b31fb-e741-4645-8ee9-8e6c7f1d3e0f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman prime Of generic Pt 22a3f75bc1e3: P2 M Ground Theory Heights  Heights Kleiman prime Of generic Pt 22a3f75bc1e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman prime Of generic Pt 22a3f75bc1e3 construction uses the P2 M Ground Theory Heights  Heights Kleiman prime Of generic Pt 22a3f75bc1e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L962-L973
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/Objects.lean#L962-L973

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_genericPt_22a3f75bc1e3 : primeOf (S := k) (genericPt k N) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«primeOf_genericPt» := P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_genericPt_22a3f75bc1e3
