-- Prove2me | Theorems.Thm_PIW_FdPA_opN_smul
-- name    : PIW.FdPA.opN_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:41.023052+00:00
-- url     : https://prove2.me/theorems/cb59eadf-f2ff-411e-8763-1a649aaf4730
-- title:
--   Fd PA: op N smul
-- statement:
--   The Fd PA construction uses the op N smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/Frames.lean#L109-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/Frames.lean#L109-L129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section

theorem PIW.FdPA.opN_smul {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) = ‖t‖ * Data.opN A := by sorry
