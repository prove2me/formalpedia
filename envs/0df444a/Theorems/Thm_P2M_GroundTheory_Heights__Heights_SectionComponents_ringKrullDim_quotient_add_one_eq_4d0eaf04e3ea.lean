-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_eq_4d0eaf04e3ea
-- name    : P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_eq_4d0eaf04e3ea
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:18:58.850101+00:00
-- url     : https://prove2.me/theorems/e347e52a-2040-482f-a5cf-faf6c548efe1
-- title:
--   P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one eq 4d0eaf04e3ea: P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one eq 4d0eaf
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one eq 4d0eaf04e3ea construction uses the P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one eq 4d0eaf04e3ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionComponents.lean#L46-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionComponents.lean#L46-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.SectionComponents
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_eq_4d0eaf04e3ea {P W : Ideal (MvPolynomial (Fin n) F)} [P.IsPrime]
    {f : MvPolynomial (Fin n) F} (hf : f ∉ P) (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionComponents».«ringKrullDim_quotient_add_one_eq» := P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_eq_4d0eaf04e3ea
