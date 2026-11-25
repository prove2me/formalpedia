-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_horizontal_0e5727bbd888
-- name    : P2M_GroundTheory_Heights__Heights_RecQOfRecursion_horizontal_0e5727bbd888
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:06:40.470256+00:00
-- url     : https://prove2.me/theorems/764e282d-1378-41a1-bc82-410a5e9e2aef
-- title:
--   P2 M Ground Theory Heights  Heights Rec QOf Recursion horizontal 0e5727bbd888: P2 M Ground Theory Heights  Heights Rec QOf Recursion horizontal 0e5727bbd888
-- statement:
--   The P2 M Ground Theory Heights  Heights Rec QOf Recursion horizontal 0e5727bbd888 construction uses the P2 M Ground Theory Heights  Heights Rec QOf Recursion horizontal 0e5727bbd888 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L129-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L129-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_HeightMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5

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
noncomputable section
open GroundTheory.Heights₂.Heights.RecQOfRecursion
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)
variable {n : ℕ}
open Classical

theorem P2M_GroundTheory_Heights__Heights_RecQOfRecursion_horizontal_0e5727bbd888 (hMul : ChowHeightMul.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    {g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ} {d : Ideal (MRing (PBlk n)) → ℕ}
    (hP : IsArithVar P (e + 1 + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P)
    (hg : ∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W)))
    (hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ))) :
    chowHt (archData S hS hconj) (e + 1) δ (specFirst f fun j => (u j : ℚ)) =
      ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
        (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
          (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RecQOfRecursion».«horizontal» := P2M_GroundTheory_Heights__Heights_RecQOfRecursion_horizontal_0e5727bbd888
