-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_linForm_not_mem_genericIdeal_6fe79e6359ca
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_linForm_not_mem_genericIdeal_6fe79e6359ca
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:31.324832+00:00
-- url     : https://prove2.me/theorems/bf1d7046-1703-4c07-b6a2-0e48d62a6295
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss lin Form not mem generic Ideal 6fe79e6359ca: P2 M Ground Theory Heights  Heights Vertical Part Gauss lin Form not mem generic Ideal 6fe79e6359ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss lin Form not mem generic Ideal 6fe79e6359ca construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss lin Form not mem generic Ideal 6fe79e6359ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L149-L156

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
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_linForm_not_mem_genericIdeal_6fe79e6359ca {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    {u : Fin n → ℤ} (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    linForm (fun j => (u j : ℚ)) ∉ genericIdeal P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«linForm_not_mem_genericIdeal» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_linForm_not_mem_genericIdeal_6fe79e6359ca
