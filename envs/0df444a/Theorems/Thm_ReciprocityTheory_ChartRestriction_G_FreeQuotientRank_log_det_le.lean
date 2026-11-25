-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_log_det_le
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.log_det_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:46.498215+00:00
-- url     : https://prove2.me/theorems/63edf018-0146-4108-b9e0-da4b182dfbf4
-- title:
--   Free Quotient Rank: log det le
-- statement:
--   The Free Quotient Rank construction uses the log det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L96-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobQuotH.lean#L96-L147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.log_det_le {ρ : ℕ} (m : Matrix (Fin ρ) (Fin ρ) K) (hdet : m.det ≠ 0) (σ : InfinitePlace K)
    (a b : Fin ρ → ℝ) (harch : ∀ i j, m i j ≠ 0 → Real.log (σ (m i j)) + a i ≤ b j) :
    Real.log (σ m.det) ≤ ∑ j, b j - ∑ i, a i + (ρ : ℝ) / 2 * Real.log ρ := by sorry
