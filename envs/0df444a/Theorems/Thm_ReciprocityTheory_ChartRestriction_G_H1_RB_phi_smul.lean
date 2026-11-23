-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_phi_smul
-- name    : ReciprocityTheory.ChartRestriction.G.H1.RB.phi_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:07.695606+00:00
-- url     : https://prove2.me/theorems/8a69eb64-3c98-446a-9e32-e68c9ae36831
-- title:
--   RB: phi smul
-- statement:
--   The RB construction uses the phi smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean#L87-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ} (u : Fin d → E) (k : Fin d)

theorem ReciprocityTheory.ChartRestriction.G.H1.RB.phi_smul (a : ℝ) (x : E) : phi u k (a • x) = a * phi u k x := by sorry
