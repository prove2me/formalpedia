-- Prove2me | Theorems.Thm_QEC_QLDPC_generatedStabilizer_cssZCheck_sum
-- name    : QEC.QLDPC.generatedStabilizer_cssZCheck_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:24:01.14618+00:00
-- url     : https://prove2.me/theorems/7ba162bb-4cee-4a0e-9e38-84192fc51703
-- title:
--   QLDPC: generated Stabilizer css ZCheck sum
-- statement:
--   Pure Z checks generated termwise also generate the check for their finite binary sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L122-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L122-L141

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.generatedStabilizer_cssZCheck_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : Type v} [Fintype κ] {alpha : Type w}
    (generators : κ → Coding.PauliSymplectic.Binary ι)
    (s : Finset alpha) (f : alpha → Coding.Word (ZMod 2) ι)
    (h : ∀ a ∈ s, Coding.PauliSymplectic.GeneratedStabilizer generators
      (Coding.PauliSymplectic.cssZCheck (f a))) :
    Coding.PauliSymplectic.GeneratedStabilizer generators
      (Coding.PauliSymplectic.cssZCheck (∑ a ∈ s, f a)) := by sorry
