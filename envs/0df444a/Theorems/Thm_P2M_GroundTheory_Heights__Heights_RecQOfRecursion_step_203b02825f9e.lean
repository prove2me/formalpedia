-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_step_203b02825f9e
-- name    : P2M_GroundTheory_Heights__Heights_RecQOfRecursion_step_203b02825f9e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:08:51.627176+00:00
-- url     : https://prove2.me/theorems/429a4afa-858b-5ae8-8f6c-4a43d6039cfc
-- title:
--   P2 M Ground Theory Heights  Heights Rec QOf Recursion step 203b02825f9e: P2 M Ground Theory Heights  Heights Rec QOf Recursion step 203b02825f9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rec QOf Recursion step 203b02825f9e construction uses the P2 M Ground Theory Heights  Heights Rec QOf Recursion step 203b02825f9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L96-L125

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

theorem P2M_GroundTheory_Heights__Heights_RecQOfRecursion_step_203b02825f9e (hRec : ChowHeightRecursionRat.Statement) (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
                              chowHt (archData S hS hconj) e δ (specFirst f fun j => (u j : ℚ)) +
                                (IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
                                  arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
                                    (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
      IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) e
        (specFirst f fun j => (u j : ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RecQOfRecursion».«step» := P2M_GroundTheory_Heights__Heights_RecQOfRecursion_step_203b02825f9e
