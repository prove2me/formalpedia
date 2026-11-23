-- Prove2me | Theorems.Thm_Reformulated_AutPerF_mem_span_of_approx
-- name    : Reformulated.AutPerF.mem_span_of_approx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:35.242862+00:00
-- url     : https://prove2.me/theorems/09230b31-ae8b-4cd5-8d2b-78a48454aa77
-- title:
--   Aut Per F: mem span of approx
-- statement:
--   The Aut Per F construction uses the mem span of approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L12-L51

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u

theorem Reformulated.AutPerF.mem_span_of_approx {A : Type*} [CommRing A] (q ξ : A) [IsAdicComplete (span {q}) A]
    (K : Set A) (h : ∀ x ∈ K, ∃ a, ∃ y ∈ K, x = ξ * a + q * y) {x : A} (hx : x ∈ K) :
    x ∈ span {ξ} := by sorry
