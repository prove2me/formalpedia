-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_haar_trace_tail
-- name    : RandomOracleUnitarySynthesis.synthesis_haar_trace_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:23.092225+00:00
-- url     : https://prove2.me/theorems/7a665de8-fafd-480e-946a-522439c4c941
-- title:
--   Lemma 4.13 — Haar trace-correlation tail
-- statement:
--   Let $A$ be any fixed Hermitian contraction on $n$ qubits and $Q$ any nonidentity phase-free Pauli operator. For every $t\ge0$ and Haar-random $U\in U(2^n)$,
--
--   $$\Pr\!\left[\frac1N\operatorname{tr}(AU^\dagger Q U)\ge t\right]\le\exp\!\left(-\frac{N^2t^2}{48}\right).$$
--
--   This is a one-sided estimate with ordinary unnormalized trace inside the displayed normalization. No separate mean-zero condition is imposed on $A$.
--
--   Differences from the source:
--   - encoding: binary computational bases and the phase-free Pauli family → Fin n → Fin 2 bases and Fin n → Fin 4 labels for tensor products of I, X, Y, Z; reason: these are bijective finite encodings of the source basis and all 4ⁿ phase-free Paulis, with the zero label equal to identity
--   - encoding: ordinary real trace of products of Hermitian operators → the real part of the ordinary complex trace; reason: conjugating and cycling the trace proves its reality without adding a hypothesis
--   - encoding: probability for a normalized Haar random full complex unitary → evaluation of Borel Haar probability with ENNReal.ofReal thresholds; reason: the measure is an actual probability and all thresholds are nonnegative in the stated domain
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.13, printed p. 30 (PDF p. 32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=32; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_haar_trace_tail (n : ℕ) (A : synthesis_Mat n)
    (hA : A.IsHermitian) (hcontract : synthesis_IsContraction A)
    (Q : synthesis_Pauli n) (hQ : Q ≠ (fun _ => 0)) (t : ℝ) (ht : 0 ≤ t) :
    (synthesis_haar n) {U | t ≤ synthesis_correlation A Q U} ≤
      ENNReal.ofReal (Real.exp (-((2 : ℝ)^n)^2 * t^2 / 48)) := by sorry

end RandomOracleUnitarySynthesis
