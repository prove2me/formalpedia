-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_generator_mem_range_linearMapOfGenerators
-- name    : QEC.Coding.QuantumTanner.generator_mem_range_linearMapOfGenerators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:03.330159+00:00
-- url     : https://prove2.me/theorems/d2478fbb-076c-4116-ad23-7c6cddb1f52e
-- title:
--   Quantum Tanner: generator mem range linear Map Of Generators
-- statement:
--   Every selected generator lies in the range of its actual generator map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L215-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L215-L220

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v

theorem QEC.Coding.QuantumTanner.generator_mem_range_linearMapOfGenerators
    {F : Type} {ι κ : Type v} [Field F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) (k : κ) :
    generator k ∈ LinearMap.range (linearMapOfGenerators generator) := by sorry
