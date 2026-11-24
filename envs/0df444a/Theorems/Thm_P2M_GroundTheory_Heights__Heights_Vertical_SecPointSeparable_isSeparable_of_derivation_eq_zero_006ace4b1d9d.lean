-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_isSeparable_of_derivation_eq_zero_006ace4b1d9d
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_isSeparable_of_derivation_eq_zero_006ace4b1d9d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:44.607042+00:00
-- url     : https://prove2.me/theorems/e759139a-277a-4183-affb-728b98102bde
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Point Separable is Separable of derivation eq zero 006ace4b1d9d: P2 M Ground Theory Heights  Heights Vertical Sec Point Separable is Separable of deriv
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Point Separable is Separable of derivation eq zero 006ace4b1d9d construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Point Separable is Separable of derivation eq zero 006ace4b1d9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecPointSeparable.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecPointSeparable.lean#L16-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenericFormsKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecPointSeparable
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
open GroundTheory.Heights₂.Heights.Vertical.SecPointSeparable

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_isSeparable_of_derivation_eq_zero_006ace4b1d9d {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecPointSeparable».«isSeparable_of_derivation_eq_zero» := P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_isSeparable_of_derivation_eq_zero_006ace4b1d9d
