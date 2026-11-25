-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_inv_lact
-- name    : ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.inv_lact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:23.550616+00:00
-- url     : https://prove2.me/theorems/ac99e931-6ea6-432a-8948-4b56578a5813
-- title:
--   Compact Entry Bounds: inv lact
-- statement:
--   The Compact Entry Bounds construction uses the inv lact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L57-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.inv_lact (γ : GL (Fin r) E) (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ * Y)⁻¹ *ᵥ Data.emb τ v =
      Y⁻¹ *ᵥ Data.emb τ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) := by sorry
