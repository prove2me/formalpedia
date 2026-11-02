-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds_gv_asymptotic_params
-- name    : QAlgorithms.GottesmanIntro.codeBounds_gv_asymptotic_params
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T19:50:00.374408+00:00
-- url     : https://prove2.me/theorems/f4a1d985-bbb9-4895-999e-37e687e440df
-- title:
--   Asymptotic parameter achievability for the quantum Gilbert–Varshamov bound
-- statement:
--   This theorem establishes the asymptotic existence of integer code parameters $(n,k,d)$ satisfying the finite quantum Gilbert–Varshamov inequality at the asymptotic Gilbert–Varshamov rate.
--
--   Let $p \in (0, 1/2)$ and $\varepsilon > 0$, and write $H_2(x) = -x\log_2 x - (1-x)\log_2(1-x)$ for the binary entropy function in bits. Then there exists $N \in \mathbb{N}$ such that for every block length $n \ge N$, if $1 - 2p\log_2 3 - H_2(2p) > 0$, there exist integers $k, d \in \mathbb{N}$ with $d \ge 1$ and $d \ge 2pn$ satisfying both the finite quantum Gilbert–Varshamov inequality
--
--   $$
--   \left(\sum_{j=0}^{d-1} 3^j \binom{n}{j}\right) 2^k \le 2^n
--   $$
--
--   and the asymptotic rate lower bound
--
--   $$
--   \frac{k}{n} \ge 1 - 2p\log_2 3 - H_2(2p) - \varepsilon.
--   $$
--
--   This isolates the analytic and combinatorial estimate behind the lower bound in equation (37) of Gottesman's Theorem 4 from the finite quantum code construction.
--
--   **Formalization Note** The binary entropy in base $2$ is represented by `binEntropy2`, and real division `(k : ℝ) / n` is used for the rate.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, https://arxiv.org/abs/0904.2557v1, pp.7–8, Theorem 4, equations (36) and (37)

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

namespace QAlgorithms.GottesmanIntro
theorem codeBounds_gv_asymptotic_params :
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ k d : ℕ, 1 ≤ d ∧ 2 * p * n ≤ d ∧
          (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n := by sorry
end QAlgorithms.GottesmanIntro
