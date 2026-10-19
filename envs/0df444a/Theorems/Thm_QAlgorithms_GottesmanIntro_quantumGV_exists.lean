-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_quantumGV_exists
-- name    : QAlgorithms.GottesmanIntro.quantumGV_exists
-- status  : Open
-- author  : @fizzyinc3
-- created : 2026-10-18T02:31:53.499993+00:00
-- url     : https://prove2.me/theorems/6485a4b9-f86c-4d3c-9da7-f3d44dcdde12
-- title:
--   Finite quantum Gilbert–Varshamov existence bound
-- statement:
--   Let $n,k,d$ be natural numbers with $d\ge1$. If
--   $$\left(\sum_{j=0}^{d-1}3^j\binom nj\right)2^k\le2^n,$$
--   then there exists a quantum $[[n,k,d]]$ code: a complex subspace of the $n$-qubit Hilbert space of dimension $2^k$ that detects every operator supported on at most $d-1$ qubits.
--
--   This is the finite existence clause of Gottesman's Theorem 4, separated from the Hamming bound and asymptotic estimates. Distance means distance at least $d$, as in the parent theorem; zero logical qubits are allowed.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, https://arxiv.org/abs/0904.2557v1, p.7, Theorem 4, equation (36)

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

namespace QAlgorithms.GottesmanIntro
theorem quantumGV_exists :
    ∀ n k d : ℕ, 1 ≤ d →
      (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n →
      ∃ C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)), IsQCode n k d C := by sorry
end QAlgorithms.GottesmanIntro
