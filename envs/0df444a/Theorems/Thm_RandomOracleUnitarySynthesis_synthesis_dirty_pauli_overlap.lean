-- Prove2me | Theorems.Thm_RandomOracleUnitarySynthesis_synthesis_dirty_pauli_overlap
-- name    : RandomOracleUnitarySynthesis.synthesis_dirty_pauli_overlap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:14.837317+00:00
-- url     : https://prove2.me/theorems/ef033073-eb4b-4848-9290-4848f86c205b
-- title:
--   Lemma 4.11 — Dirty-channel Pauli overlap
-- statement:
--   Fix a circuit, a Boolean function $f$, and any unitary $U$ on the $n$-qubit system. For $P$ uniform over all $4^n$ phase-free Pauli operators, put $A_{f,P}=J^\dagger W_f^\dagger(P\otimes I)W_fJ$. Then
--
--   $$\mathbb E_P\frac1N\operatorname{tr}(A_{f,P}U^\dagger P U)\ge1-D_\diamond(E_f,\Phi_U).$$
--
--   The channel $E_f$ traces out garbage ancillas. The inequality uses its actual diamond distance and requires neither a synthesis coupling nor a prescribed error tolerance.
--
--   Differences from the source:
--   - encoding: binary computational bases, Boolean truth tables, and the stated register inequalities → Fin n → Fin 2 bases, Bool-valued truth tables, and a circuit type carrying n ≤ m and m₀ ≤ m; reason: these are bijective finite encodings of exactly the source registers and functions
--   - encoding: uniform finite expectations → normalized finite sums and genuine PMF expectations; reason: the truth-table and seed sets are finite and nonempty, so the sums equal the source expectations
--   - encoding: ordinary real trace of products of Hermitian operators → the real part of the ordinary complex trace; reason: conjugating and cycling the trace proves its reality without adding a hypothesis
--   - encoding: channels and their all-finite-reference diamond distance → matrix-unit channel coordinates and the literal mixed-state all-reference supremum; reason: coordinates identify the same linear maps and preserve the source distance including its factor one half
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Lemma 4.11, printed p. 26 (PDF p. 28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=28; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit

open scoped Matrix ComplexConjugate
open MeasureTheory Filter Classical
noncomputable section

namespace RandomOracleUnitarySynthesis

theorem synthesis_dirty_pauli_overlap {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (U : synthesis_Unitary n) :
    1 - synthesis_diamond (synthesis_actualChannel C f) (synthesis_unitaryChannel U) ≤
      synthesis_average (fun P : synthesis_Pauli n =>
        synthesis_correlation (synthesis_observable C f P) P U) := by sorry

end RandomOracleUnitarySynthesis
