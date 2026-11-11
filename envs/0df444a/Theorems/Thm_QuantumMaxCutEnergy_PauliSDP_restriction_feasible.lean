-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_restriction_feasible
-- name    : QuantumMaxCutEnergy.PauliSDP.restriction_feasible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:54:34.836659+00:00
-- url     : https://prove2.me/theorems/9c0c11fc-0e6a-41cb-b165-548dd103581a
-- title:
--   Restricting a level-$k$ Pauli moment functional to at most $k$ qubits
-- statement:
--   Let $L$ be feasible for the level-$k$ Pauli moment relaxation on $n$ qubits, and let $\iota:\{0,\dots,s-1\}\to\{0,\dots,n-1\}$ be injective with $s\le k$. For a Pauli word $P$ on $s$ qubits let $\iota_*P$ be the word on $n$ qubits that carries $P_a$ at site $\iota(a)$ and the identity elsewhere. Then $L'(P)=L(\iota_*P)$ is feasible for the level-$s$ relaxation on $s$ qubits, whose Gram matrix is indexed by all $4^s$ words.
--
--   The Gram matrix of $L'$ is a principal submatrix of that of $L$, since $\iota_*$ preserves products and phases of words.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv:2504.11120v1, Section 3, proof of Corollary 3.6 (restriction of a feasible moment functional to a subset of qubits).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.restriction_feasible {n k s : ℕ}
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L)
    (ι : Fin s → Fin n) (hι : Function.Injective ι) (hs : s ≤ k) :
    QuantumMaxCutEnergy.PauliSDP.Feasible s
      (fun P : QuantumMaxCutEnergy.PauliSDP.Word s =>
        L (Function.extend ι P (fun _ => 0))) := by sorry
