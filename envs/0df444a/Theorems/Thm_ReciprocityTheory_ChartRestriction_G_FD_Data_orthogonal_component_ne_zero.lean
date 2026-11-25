-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_orthogonal_component_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.orthogonal_component_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:31.824358+00:00
-- url     : https://prove2.me/theorems/e550d32e-9606-4042-b2a2-657060fb4311
-- title:
--   Data: orthogonal component ne zero
-- statement:
--   The Data construction uses the orthogonal component ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankEqTwoMulHalfDegree.lean#L44-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.orthogonal_component_ne_zero (z : Frame X.Ψ r) {ξ x : Fin r → E} (hξ : ξ ≠ 0) (hx : ∀ e : E, x ≠ e • ξ)
    (τ : X.Ψ) : X.ucomp z ξ (X.embV x) τ ≠ 0 := by sorry
