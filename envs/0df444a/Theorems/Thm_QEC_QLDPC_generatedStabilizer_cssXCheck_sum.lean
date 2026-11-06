-- Prove2me | Theorems.Thm_QEC_QLDPC_generatedStabilizer_cssXCheck_sum
-- name    : QEC.QLDPC.generatedStabilizer_cssXCheck_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:54.952882+00:00
-- url     : https://prove2.me/theorems/3ab725c1-d776-442a-83d2-694fdbeb94af
-- title:
--   QLDPC: generated Stabilizer css XCheck sum
-- statement:
--   Pure X checks generated termwise also generate the check for their finite binary sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L100-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L100-L119

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.generatedStabilizer_cssXCheck_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : Type v} [Fintype κ] {alpha : Type w}
    (generators : κ → Coding.PauliSymplectic.Binary ι)
    (s : Finset alpha) (f : alpha → Coding.Word (ZMod 2) ι)
    (h : ∀ a ∈ s, Coding.PauliSymplectic.GeneratedStabilizer generators
      (Coding.PauliSymplectic.cssXCheck (f a))) :
    Coding.PauliSymplectic.GeneratedStabilizer generators
      (Coding.PauliSymplectic.cssXCheck (∑ a ∈ s, f a)) := by sorry
