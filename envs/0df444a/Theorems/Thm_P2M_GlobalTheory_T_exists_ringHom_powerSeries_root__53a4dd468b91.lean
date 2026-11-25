-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_ringHom_powerSeries_root__53a4dd468b91
-- name    : P2M_GlobalTheory_T_exists_ringHom_powerSeries_root__53a4dd468b91
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:50.823841+00:00
-- url     : https://prove2.me/theorems/6f142bd7-c62e-4983-b434-b46a11d185a2
-- title:
--   P2 M Global Theory T exists ring Hom power Series root  53a4dd468b91: P2 M Global Theory T exists ring Hom power Series root  53a4dd468b91
-- statement:
--   The P2 M Global Theory T exists ring Hom power Series root  53a4dd468b91 construction uses the P2 M Global Theory T exists ring Hom power Series root  53a4dd468b91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRootStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRootStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRootStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_ringHom_powerSeries_root__53a4dd468b91 : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by sorry

alias «GlobalTheory».«T».«exists_ringHom_powerSeries_root'» := P2M_GlobalTheory_T_exists_ringHom_powerSeries_root__53a4dd468b91
