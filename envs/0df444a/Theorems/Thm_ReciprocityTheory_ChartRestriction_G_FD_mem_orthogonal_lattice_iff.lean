-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_mem_orthogonal_lattice_iff
-- name    : ReciprocityTheory.ChartRestriction.G.FD.mem_orthogonal_lattice_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:17.286503+00:00
-- url     : https://prove2.me/theorems/931f93c8-4b8c-5247-b992-d11c5b62e96d
-- title:
--   FD: mem orthogonal lattice iff
-- statement:
--   The FD construction uses the mem orthogonal lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermEqZeroOfTraceFormVanish.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermEqZeroOfTraceFormVanish.lean#L9-L10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.mem_orthogonal_lattice_iff {r : ℕ} (X : Data E r) (ξ v : Fin r → E) :
    v ∈ X.Λp ξ ↔ v ∈ X.Λ ∧ herm X.Gm v ξ = 0 := by sorry
