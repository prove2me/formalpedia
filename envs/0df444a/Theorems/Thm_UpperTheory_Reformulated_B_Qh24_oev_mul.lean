-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qh24_oev_mul
-- name    : UpperTheory.Reformulated.B.Qh24.oev_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:23.566886+00:00
-- url     : https://prove2.me/theorems/0c2de060-2ba3-489c-a15c-e2c808132cf4
-- title:
--   Qh24: oev mul
-- statement:
--   The Qh24 construction uses the oev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InclR.lean#L42-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InclR.lean#L42-L65

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InclR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qh24.oev_mul :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      {s t : TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E},
      s ∈ UpperTheory.Reformulated.B.Qh24.OEv v → t ∈ UpperTheory.Reformulated.B.Qh24.OEv v → s * t ∈ UpperTheory.Reformulated.B.Qh24.OEv v := by sorry
