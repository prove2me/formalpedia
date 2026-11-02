-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_polyProgram_of_tm2InPolyTime
-- name    : QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:50:36.814465+00:00
-- url     : https://prove2.me/theorems/1f786a26-2359-4f06-8fa9-89f4b509f72c
-- title:
--   Boolean-stack program bridge for a nonnegative-rational TM2 certificate
-- statement:
--   Let $f$ be a function from an encoded input type to nonnegative rational numbers, and suppose $f$ has a genuine polynomial-time multi-tape Turing-machine certificate on the campaign's canonical output encoding $\mathrm{encodeValue}$. Then $f$ has a polynomial-time certificate in the campaign's concrete Boolean-stack programming language `PolyProgram`, in the library's canonical ratio encoding.
--
--   This packages the two finite-bit implementation steps that the campaign's runtime library supplies only in the reverse direction: (i) simulating a multi-tape machine whose internal stack alphabets are arbitrary finite types by a machine with Boolean stacks, with polynomial overhead, and (ii) recomputing the campaign's self-delimiting integer frame $\mathsf{frame}(x) = 1^{|x|}0x$ into the numerator/denominator ratio frame used by the library's arithmetic programs. Both are explicit finite-bit polynomial-time computations; no approximation, no numerical precision and no probability is involved.
-- source:
--   Not a quoted paper result. Formalizes the simulation direction missing from Mathlib 0df444a: `Turing.TM2ComputableInPolyTime.comp` is a `proof_wanted` there, and the campaign module Def_QuantumMaxCutFiniteNumericRuntime only provides `OAI.MetricKMedian.Binary.PolyProgram.stock` (program to machine), not the converse. Needed to discharge QuantumMaxCutEnergy.polynomialTime_max_with_deterministic_estimator.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
open scoped BigOperators

theorem QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime
    {α : Type} (ea : α → List Bool) (f : α → ℚ≥0)
    (h : Turing.TM2ComputableInPolyTime ea QuantumMaxCutEnergy.encodeValue f) :
    Nonempty (OAI.MetricKMedian.Binary.PolyProgram ea
      (fun q : ℚ≥0 => OAI.MetricKMedian.Binary.Ratio.encode (q : ℚ)) f) := by sorry
