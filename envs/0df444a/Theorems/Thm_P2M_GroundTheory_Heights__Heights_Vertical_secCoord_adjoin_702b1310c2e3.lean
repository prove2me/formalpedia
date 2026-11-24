-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secCoord_adjoin_702b1310c2e3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_secCoord_adjoin_702b1310c2e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:51.512631+00:00
-- url     : https://prove2.me/theorems/346aa993-3915-4bef-a7b0-88cc0d205d88
-- title:
--   P2 M Ground Theory Heights  Heights Vertical sec Coord adjoin 702b1310c2e3: P2 M Ground Theory Heights  Heights Vertical sec Coord adjoin 702b1310c2e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical sec Coord adjoin 702b1310c2e3 construction uses the P2 M Ground Theory Heights  Heights Vertical sec Coord adjoin 702b1310c2e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormFormGeneric.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowNormFormGeneric.lean#L23-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowNormFormGeneric
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_secCoord_adjoin_702b1310c2e3 {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«secCoord_adjoin» := P2M_GroundTheory_Heights__Heights_Vertical_secCoord_adjoin_702b1310c2e3
