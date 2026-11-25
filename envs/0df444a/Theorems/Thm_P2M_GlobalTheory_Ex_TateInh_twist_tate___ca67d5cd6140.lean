-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Ex_TateInh_twist_tate___ca67d5cd6140
-- name    : P2M_GlobalTheory_Ex_TateInh_twist_tate___ca67d5cd6140
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:12:34.988592+00:00
-- url     : https://prove2.me/theorems/ffe45cb2-c620-567e-9126-9d3470045001
-- title:
--   P2 M Global Theory Ex Tate Inh twist tate   ca67d5cd6140: P2 M Global Theory Ex Tate Inh twist tate   ca67d5cd6140
-- statement:
--   The P2 M Global Theory Ex Tate Inh twist tate   ca67d5cd6140 construction uses the P2 M Global Theory Ex Tate Inh twist tate   ca67d5cd6140 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L232-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L232-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh

theorem P2M_GlobalTheory_Ex_TateInh_twist_tate___ca67d5cd6140 (q u : Oˣ) (k : ℕ) (hk : k ≠ 0) (n : ℤ) :
    ((tate q).twist (tateBe q k hk) u).ψ n = (tate (q * u ^ k)).ψ n := by sorry

alias «GlobalTheory».«Ex».«TateInh».«twist_tate_ψ» := P2M_GlobalTheory_Ex_TateInh_twist_tate___ca67d5cd6140
