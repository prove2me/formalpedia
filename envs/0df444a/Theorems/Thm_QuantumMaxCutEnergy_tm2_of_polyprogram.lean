-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_tm2_of_polyprogram
-- name    : QuantumMaxCutEnergy.tm2_of_polyprogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:55:57.541949+00:00
-- url     : https://prove2.me/theorems/af08e667-9ad5-4c7d-a8a9-90c4ecf54c64
-- title:
--   A PolyProgram is a polynomial-time multi-tape machine
-- statement:
--   **A `PolyProgram` is a polynomial-time multi-tape machine.**
--
--   The campaign's runtime fixes a Boolean-stack programming language (`PolyProgram`) with its own polynomial-time semantics: a program carries a finite `Machine`, a polynomial `time`, and for every input `a` a proof that the machine halts with output `eb (f a)` within `time.eval (ea a).length` steps. `PolyProgram.stock` turns it into the multi-tape certificate `TM2ComputableInPolyTime ea eb f` with the same machine and the same polynomial.
--
--   Consequently the machine obligation of `agm_classical_sdp_lower_value_tm2` is discharged by building a `PolyProgram`, using the runtime's fixed-point rational arithmetic (`Ratio.encode`, `nnratOutput`, `rationalMaximumProgram`, …), rather than by hand-writing a TM2 machine.
-- source:
--   OAI.MetricKMedian.Binary.PolyProgram.stock, in Definitions.Def_QuantumMaxCutFiniteNumericRuntime (ported from OpenAI math, revision 4eaee87548250b2682affda7d05d947c05554bae, Apache-2.0).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix

open scoped BigOperators

namespace QuantumMaxCutEnergy

open OAI.MetricKMedian.Binary

/-- **Every `PolyProgram` is a polynomial-time `TM2` machine.** The runtime's Boolean-stack
language compiles to the multi-tape model by `PolyProgram.stock`, so the machine half of
`agm_classical_sdp_lower_value_tm2` may be discharged by building a `PolyProgram`. -/
theorem tm2_of_polyprogram {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by sorry

end QuantumMaxCutEnergy
