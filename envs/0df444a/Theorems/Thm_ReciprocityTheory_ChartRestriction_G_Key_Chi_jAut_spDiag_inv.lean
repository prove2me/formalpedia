-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_spDiag_inv
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut_spDiag_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:48.177907+00:00
-- url     : https://prove2.me/theorems/1dc7a76c-1ba4-4a35-882a-95345227d70b
-- title:
--   Chi: j Aut sp Diag inv
-- statement:
--   The Chi construction uses the j Aut sp Diag inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L140-L144

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut_spDiag_inv {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (jAut (spDiag U) τ)⁻¹ = ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by sorry
