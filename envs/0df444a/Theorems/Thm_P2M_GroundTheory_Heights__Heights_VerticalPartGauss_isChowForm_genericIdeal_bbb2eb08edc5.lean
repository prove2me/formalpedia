-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isChowForm_genericIdeal_bbb2eb08edc5
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isChowForm_genericIdeal_bbb2eb08edc5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:50.146554+00:00
-- url     : https://prove2.me/theorems/84e21227-8747-417a-9838-6bee5b6b3ee3
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss is Chow Form generic Ideal bbb2eb08edc5: P2 M Ground Theory Heights  Heights Vertical Part Gauss is Chow Form generic Ideal bbb2eb08edc5
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss is Chow Form generic Ideal bbb2eb08edc5 construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss is Chow Form generic Ideal bbb2eb08edc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L160-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L160-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isChowForm_genericIdeal_bbb2eb08edc5 {n e δ : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1))
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) :
    IsChowForm (genericIdeal P) (e + 1) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«isChowForm_genericIdeal» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isChowForm_genericIdeal_bbb2eb08edc5
