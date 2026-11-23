-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_spDiag
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat_spDiag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:58.637301+00:00
-- url     : https://prove2.me/theorems/1a0836cf-3e00-47ca-9c0f-53c7b6530480
-- title:
--   Chi: c Mat sp Diag
-- statement:
--   The Chi construction uses the c Mat sp Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L121-L124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat_spDiag {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) :
    cMat (spDiag U) = Matrix.fromBlocks ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ))) 0 0
      (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by sorry
