-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds_asymptotic_of_hamming
-- name    : QAlgorithms.GottesmanIntro.codeBounds_asymptotic_of_hamming
-- status  : Open
-- author  : @fizzyinc3
-- created : 2026-10-18T02:32:28.308093+00:00
-- url     : https://prove2.me/theorems/954206e7-64e6-4829-99bf-33c9a5d784e8
-- title:
--   Asymptotic nondegenerate quantum code rates from the finite Hamming bound
-- statement:
--   Assume the finite quantum Hamming bound: every nondegenerate quantum $[[n,k,d]]$ code, with $t=\lfloor(d-1)/2\rfloor$, satisfies $2^k\sum_{j=0}^{t}3^j\binom nj\le2^n$. Let $0<p<1/2$ and $\varepsilon>0$. For every sufficiently large block length $n$, the following hold:
--
--   1. Every such nondegenerate code with $d\ge2pn$ has rate
--   $$\frac{k}{n}\le1-p\log_2 3-H(p)+\varepsilon.$$
--   2. If $1-2p\log_2 3-H(2p)>0$, a nondegenerate code exists with $d\ge2pn$ and rate
--   $$\frac{k}{n}\ge1-2p\log_2 3-H(2p)-\varepsilon.$$
--
--   Here $H(x)=-x\log_2x-(1-x)\log_2(1-x)$ is binary entropy. This is the rate window in Gottesman's Theorem 4, equation (37), with the finite Hamming inequality exposed as an input so its established proof can be reused. The block-length threshold may depend on $p$ and $\varepsilon$.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, https://arxiv.org/abs/0904.2557v1, pp.7–8, Theorem 4, equation (37)

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

namespace QAlgorithms.GottesmanIntro
theorem codeBounds_asymptotic_of_hamming (hamming : ∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) :
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε) ∧
      (0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C ∧
          IsNondegenerate C ((d - 1) / 2) ∧ 2 * p * n ≤ d ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n) := by sorry
end QAlgorithms.GottesmanIntro
