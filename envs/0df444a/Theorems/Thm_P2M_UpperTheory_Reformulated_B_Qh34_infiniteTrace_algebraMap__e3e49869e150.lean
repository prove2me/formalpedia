-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh34_infiniteTrace_algebraMap__e3e49869e150
-- name    : P2M_UpperTheory_Reformulated_B_Qh34_infiniteTrace_algebraMap__e3e49869e150
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:10.266339+00:00
-- url     : https://prove2.me/theorems/fd394b79-d153-453b-8e0a-ee7c4812f123
-- title:
--   P2 M Upper Theory Reformulated B Qh34 infinite Trace algebra Map  e3e49869e150: P2 M Upper Theory Reformulated B Qh34 infinite Trace algebra Map  e3e49869e150
-- statement:
--   The P2 M Upper Theory Reformulated B Qh34 infinite Trace algebra Map  e3e49869e150 construction uses the P2 M Upper Theory Reformulated B Qh34 infinite Trace algebra Map  e3e49869e150 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean#L38-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean#L38-L67

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteTraceAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qh34_infiniteTrace_algebraMap__e3e49869e150.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (k : K),
      (UpperTheory.Reformulated.B.Qh34.infiniteTrace K : NumberField.InfiniteAdeleRing K → ℝ)
          ((Algebra.algebraMap K (NumberField.InfiniteAdeleRing K) : K → NumberField.InfiniteAdeleRing K) k) =
        (↑((Algebra.trace ℚ K : K → ℚ) k) : ℝ) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qh34».«infiniteTrace_algebraMap».«» := P2M_UpperTheory_Reformulated_B_Qh34_infiniteTrace_algebraMap__e3e49869e150
