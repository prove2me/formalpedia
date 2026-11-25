-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_cont_gram__06583ee5c83d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_cont_gram__06583ee5c83d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:18:22.135393+00:00
-- url     : https://prove2.me/theorems/7036c808-e821-593c-adc8-ac4efb673a1b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Compact Entry Bounds cont gram  06583ee5c83d: P2 M Reciprocity Theory Chart Restriction G FD Compact Entry Bounds cont gram  06583ee5c83d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Compact Entry Bounds cont gram  06583ee5c83d construction uses the P2 M Reciprocity Theory Chart Restriction G FD Compact Entry Bounds cont gram  06583ee5c83d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CompactEntryBounds.lean#L160-L164

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_cont_gram__06583ee5c83d (τ : X.Ψ) : Continuous fun w : Frame X.Ψ r => gram τ.1 X.Gm (mat w τ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«CompactEntryBounds».«cont_gram'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_cont_gram__06583ee5c83d
