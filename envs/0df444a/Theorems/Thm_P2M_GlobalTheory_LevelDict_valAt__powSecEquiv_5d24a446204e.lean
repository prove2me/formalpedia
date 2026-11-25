-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LevelDict_valAt__powSecEquiv_5d24a446204e
-- name    : P2M_GlobalTheory_LevelDict_valAt__powSecEquiv_5d24a446204e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:47:43.287303+00:00
-- url     : https://prove2.me/theorems/acf90844-c132-5aa8-ab2f-e82593814f91
-- title:
--   P2 M Global Theory Level Dict val At  pow Sec Equiv 5d24a446204e: P2 M Global Theory Level Dict val At  pow Sec Equiv 5d24a446204e
-- statement:
--   The P2 M Global Theory Level Dict val At  pow Sec Equiv 5d24a446204e construction uses the P2 M Global Theory Level Dict val At  pow Sec Equiv 5d24a446204e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LineBundlePowSectionsEqThetaLevel.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LineBundlePowSectionsEqThetaLevel.lean#L63-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
variable {X : Scheme.{0}} (L : LB X) (n : ℕ)

theorem P2M_GlobalTheory_LevelDict_valAt__powSecEquiv_5d24a446204e (s : (lbPow L n).Sec) (x : Sp ℂ ⟶ X) (j : (lbPow L n).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    valAt' x (L.U (j PUnit.unit)) ((powSecEquiv L n s).f (j PUnit.unit)) = valAt' x ((lbPow L n).U j) (s.f j) := by sorry

alias «GlobalTheory».«LevelDict».«valAt'_powSecEquiv» := P2M_GlobalTheory_LevelDict_valAt__powSecEquiv_5d24a446204e
