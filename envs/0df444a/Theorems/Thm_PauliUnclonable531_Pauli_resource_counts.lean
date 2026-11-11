-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_resource_counts
-- name    : PauliUnclonable531.Pauli.resource_counts
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-10T09:01:47.561199+00:00
-- url     : https://prove2.me/theorems/9fb0e523-2529-45b1-8a24-8c79e4a62ece
-- title:
--   §3.1 — resource counts of the encryption and decryption procedures
-- statement:
--   Fix $n\ge1$ and a nonidentity Pauli key $k=(x,z)$ on $n$ qubits. The generated §3.1 procedures satisfy the following resource bounds.
--
--   1. The pivot found by the left-to-right key scan exists and is the least nonidentity position: it is a position $p$ with $(x_p,z_p)\ne(0,0)$ and $(x_i,z_i)=(0,0)$ for all $i<p$.
--   2. The random tapes (bit strings vanishing at the pivot) number exactly $2^{n-1}$.
--   3. The encryption instruction list contains exactly $n-1$ fair coin draws, exactly $n$ computational-basis preparations, and at most $2n$ $H/S$ gates.
--   4. Its classical address-bit cost $10(n+1)\,(n+L_{\mathrm{enc}}+1)$, with $L_{\mathrm{enc}}$ the instruction-list length, is at most $100(n+1)^2$.
--   5. The decryption instruction list has at most $n$ local Pauli measurements, and its cost $10(n+1)(n+2L_{\mathrm{dec}}+1)$ is at most $100(n+1)^2$.
--
--   These are the efficiency claims of Theorem 1.1: encryption and decryption run in time $O(n^2)$ in the declared bit-cost model, using $n-1$ random bits, $n$ basis preparations and $O(n)$ single-qubit Clifford gates or measurements.
--
--   **Formalization Note.** The counts are of the concrete instruction lists `encProgram k` and `decProgram k`; the cost functions `encBitCost` and `decBitCost` are the mission's declared address-bit cost model, in which each wire address occupies $n+1$ bits.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits and real Born probabilities; reason: these are the same finite-dimensional objects after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026) / arXiv:2607.21551v4, Theorem 1.1 (efficiency clause), p.3, and §3.1, pp.16–17

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem resource_counts (n : ℕ) (hn : 1 ≤ n) (k : Key n) :
    (∃ j, pivot k = some j ∧ active k.val j = true ∧
      ∀ i : Fin n, i < j → active k.val i = false) ∧
    Fintype.card (Tape k) = 2^(n-1) ∧
    fairCount (encProgram k) = n-1 ∧ preparationCount (encProgram k) = n ∧
    gateCount (encProgram k) ≤ 2*n ∧ encBitCost k ≤ 100*(n+1)^2 ∧
    (decProgram k).length ≤ n ∧ decBitCost k ≤ 100*(n+1)^2 := by sorry

end PauliUnclonable531.Pauli
