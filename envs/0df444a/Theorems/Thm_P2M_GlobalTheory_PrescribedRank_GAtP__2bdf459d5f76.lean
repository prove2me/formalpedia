-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PrescribedRank_GAtP__2bdf459d5f76
-- name    : P2M_GlobalTheory_PrescribedRank_GAtP__2bdf459d5f76
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:11.002597+00:00
-- url     : https://prove2.me/theorems/6cb50b6f-8a5f-44f0-8fa6-9734c8852924
-- title:
--   P2 M Global Theory Prescribed Rank GAt P  2bdf459d5f76: P2 M Global Theory Prescribed Rank GAt P  2bdf459d5f76
-- statement:
--   The P2 M Global Theory Prescribed Rank GAt P  2bdf459d5f76 construction uses the P2 M Global Theory Prescribed Rank GAt P  2bdf459d5f76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L128-L132

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

theorem P2M_GlobalTheory_PrescribedRank_GAtP__2bdf459d5f76 : ∀ (p d : ℕ), p.Prime → ∃ G : GAtP p, G.d = d ∧ G.FinClasses := by sorry

alias «GlobalTheory».«PrescribedRank».«GAtP₂» := P2M_GlobalTheory_PrescribedRank_GAtP__2bdf459d5f76
