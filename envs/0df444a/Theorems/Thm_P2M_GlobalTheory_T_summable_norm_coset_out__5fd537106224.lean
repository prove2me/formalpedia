-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_summable_norm_coset_out__5fd537106224
-- name    : P2M_GlobalTheory_T_summable_norm_coset_out__5fd537106224
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:20.376731+00:00
-- url     : https://prove2.me/theorems/363c7772-2512-5931-82fe-6a53075f447e
-- title:
--   P2 M Global Theory T summable norm coset out  5fd537106224: P2 M Global Theory T summable norm coset out  5fd537106224
-- statement:
--   The P2 M Global Theory T summable norm coset out  5fd537106224 construction uses the P2 M Global Theory T summable norm coset out  5fd537106224 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SummableNormCosetOutStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SummableNormCosetOutStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SummableNormCosetOut
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SummableNormCosetOutStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_summable_norm_coset_out__5fd537106224 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by sorry

alias «GlobalTheory».«T».«summable_norm_coset_out'» := P2M_GlobalTheory_T_summable_norm_coset_out__5fd537106224
