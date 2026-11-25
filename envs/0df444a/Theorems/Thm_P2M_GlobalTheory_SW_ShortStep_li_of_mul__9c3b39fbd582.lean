-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_ShortStep_li_of_mul__9c3b39fbd582
-- name    : P2M_GlobalTheory_SW_ShortStep_li_of_mul__9c3b39fbd582
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:56.082508+00:00
-- url     : https://prove2.me/theorems/e18bb80d-750b-47c0-92d4-9fbbc461fe35
-- title:
--   P2 M Global Theory SW Short Step li of mul  9c3b39fbd582: P2 M Global Theory SW Short Step li of mul  9c3b39fbd582
-- statement:
--   The P2 M Global Theory SW Short Step li of mul  9c3b39fbd582 construction uses the P2 M Global Theory SW Short Step li of mul  9c3b39fbd582 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L224-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_SW_ShortStep_li_of_mul__9c3b39fbd582 {m n : ℕ} {B : Matrix (Fin m) (Fin n) E} (h : LinearIndependent E fun i => B i)
    {k : E} (hk : k ≠ 0) : LinearIndependent E fun i => (k • B) i := by sorry

alias «GlobalTheory».«SW».«ShortStep».«li_of_mul'» := P2M_GlobalTheory_SW_ShortStep_li_of_mul__9c3b39fbd582
