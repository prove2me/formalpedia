-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPsiBounds_Qy_smul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.Qy_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:31:41.194167+00:00
-- url     : https://prove2.me/theorems/ae69865d-589b-446d-99af-59b977266314
-- title:
--   Hermitian Psi Bounds: Qy smul
-- statement:
--   The Hermitian Psi Bounds construction uses the Qy smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPsiBounds.lean#L110-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPsiBounds.lean#L110-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.Qy_smul (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (p : Fin r → E) :
    Qy X y (α • p) ≤ (∑ τ : X.Ψ, ‖τ.1 α‖ ^ 2) * Qy X y p := by sorry
