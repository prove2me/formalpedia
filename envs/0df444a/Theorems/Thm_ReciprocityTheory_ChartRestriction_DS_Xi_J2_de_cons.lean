-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_cons
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_cons
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:29.537303+00:00
-- url     : https://prove2.me/theorems/4e770f4a-a641-5ecf-8f6e-a821bcb675f7
-- title:
--   J2: de cons
-- statement:
--   The J2 construction uses the de cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L73-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_cons {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    de ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by sorry
