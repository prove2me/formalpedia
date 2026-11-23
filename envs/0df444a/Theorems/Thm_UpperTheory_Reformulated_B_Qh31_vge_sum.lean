-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qh31_vge_sum
-- name    : UpperTheory.Reformulated.B.Qh31.vge_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:24.011264+00:00
-- url     : https://prove2.me/theorems/cfbe917d-2ce6-4639-b17f-8c23e05886e5
-- title:
--   Qh31: vge sum
-- statement:
--   The Qh31 construction uses the vge sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapCastMono.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapCastMono.lean#L16-L28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qh31.vge_sum :
    ∀ {K : Type} [inst : Field K] (v : AddValuation K (WithTop ℚ)) {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qh31.vge v a (f i)) → UpperTheory.Reformulated.B.Qh31.vge v a (∑ i ∈ s, f i) := by sorry
