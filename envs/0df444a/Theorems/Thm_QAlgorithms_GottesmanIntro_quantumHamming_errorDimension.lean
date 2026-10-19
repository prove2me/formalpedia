-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_quantumHamming_errorDimension
-- name    : QAlgorithms.GottesmanIntro.quantumHamming_errorDimension
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T02:31:56.425982+00:00
-- url     : https://prove2.me/theorems/6da5dae0-1239-4af4-b034-88d0b4aa785e
-- title:
--   Nondegenerate Pauli error images obey the quantum Hamming dimension bound
-- statement:
--   Let $C$ be a quantum $[[n,k,d]]$ code and set $t=\lfloor(d-1)/2\rfloor$. Let $\mathcal E_t$ be the finite set of phase-free tensor products of $I,X,Y,Z$ with at most $t$ nonidentity factors. If the Gram matrix of the error images $\{E\psi:E\in\mathcal E_t\}$ is nonsingular for each unit codeword $\psi$, then
--   $$|\mathcal E_t|\,2^k\le2^n.$$
--   This is the dimension argument underlying Gottesman's quantum Hamming bound. It leaves the explicit combinatorial evaluation of $|\mathcal E_t|$ to the parent reduction and can be reused independently of that enumeration. The code has distance at least $d$, and all natural block lengths, logical dimensions, and distances, including zero, are covered.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, https://arxiv.org/abs/0904.2557v1, p.7, counting argument preceding equation (35), Theorem 4.

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

namespace QAlgorithms.GottesmanIntro
theorem quantumHamming_errorDimension {n k d : ℕ}
    (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)))
    (hC : IsQCode n k d C) (hnd : IsNondegenerate C ((d-1)/2)) :
    Fintype.card {o : Fin n → Pauli // opsWeight o ≤ (d-1)/2} * 2^k ≤ 2^n := by sorry
end QAlgorithms.GottesmanIntro
