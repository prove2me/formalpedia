-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_theta_sq_red
-- name    : ReciprocityTheory.ChartRestriction.G.Key.Chi.theta_sq_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:27.658503+00:00
-- url     : https://prove2.me/theorems/7577d316-04f5-4193-aa6d-943c305b2983
-- title:
--   Chi: theta sq red
-- statement:
--   The Chi construction uses the theta sq red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L40-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/OfRealVecHalfVec.lean#L40-L60

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

theorem ReciprocityTheory.ChartRestriction.G.Key.Chi.theta_sq_red {g : ℕ} (k k' : Fin g → ℤ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 =
      theta (halfVec fun i => k i % 2) (halfVec fun i => k' i % 2) z τ ^ 2 := by sorry
