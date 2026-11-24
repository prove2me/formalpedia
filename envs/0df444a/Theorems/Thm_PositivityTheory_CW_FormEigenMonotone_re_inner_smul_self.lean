-- Prove2me | Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_re_inner_smul_self
-- name    : PositivityTheory.CW.FormEigenMonotone.re_inner_smul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:15.2303+00:00
-- url     : https://prove2.me/theorems/c7a6fc26-1f96-4a9b-8a74-db41a1500ba5
-- title:
--   Form Eigen Monotone: re inner smul self
-- statement:
--   The Form Eigen Monotone construction uses the re inner smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/BasisSumOfOrthogonality.lean#L45-L48

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}

theorem PositivityTheory.CW.FormEigenMonotone.re_inner_smul_self (r : ℝ) (v : V) : (inner ℂ v ((r : ℂ) • v)).re = r * ‖v‖ ^ 2 := by sorry
