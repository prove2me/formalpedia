-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds_hamming_asymptotic
-- name    : QAlgorithms.GottesmanIntro.codeBounds_hamming_asymptotic
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T19:50:00.626983+00:00
-- url     : https://prove2.me/theorems/71546239-0fec-4a74-8b8b-b5a2cf91b9f3
-- title:
--   Asymptotic quantum Hamming upper bound on code rate
-- statement:
--   This theorem establishes the asymptotic quantum Hamming upper bound on the rate of nondegenerate quantum error-correcting codes.
--
--   Assume the finite quantum Hamming bound: for every nondegenerate $[[n,k,d]]$ quantum code $C$ with $t=\lfloor(d-1)/2\rfloor$,
--
--   $$
--   \left(\sum_{j=0}^{t} 3^j \binom{n}{j}\right) 2^k \le 2^n.
--   $$
--
--   Let $p \in (0, 1/2)$ and $\varepsilon > 0$. Write $H_2(p) = -p\log_2 p - (1-p)\log_2(1-p)$ for the binary entropy function in bits. Then there exists a threshold $N \in \mathbb{N}$ such that for all $n \ge N$ and every nondegenerate $[[n,k,d]]$ quantum code $C$ satisfying $d \ge 2pn$,
--
--   $$
--   \frac{k}{n} \le 1 - p\log_2 3 - H_2(p) + \varepsilon.
--   $$
--
--   This provides the upper bound in the asymptotic rate window (eq. (37)) of Gottesman's Theorem 4, deduced purely from the finite quantum Hamming inequality.
--
--   **Formalization Note** The finite quantum Hamming inequality is taken as an explicit hypothesis `hamming`, and $H_2(p)$ is represented by `binEntropy2 p`.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, https://arxiv.org/abs/0904.2557v1, pp.7–8, Theorem 4, equations (35) and (37)

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

namespace QAlgorithms.GottesmanIntro
theorem codeBounds_hamming_asymptotic
    (hamming : ∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) :
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε := by sorry
end QAlgorithms.GottesmanIntro
