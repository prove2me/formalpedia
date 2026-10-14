-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_mmwu_regret
-- name    : QAlgorithms.Nannicini.mmwu_regret
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:09.261113+00:00
-- url     : https://prove2.me/theorems/a029fb5b-cf70-4d5e-a99f-89e6cd8acc6e
-- title:
--   Regret bound of the matrix multiplicative weights update
-- statement:
--   Let $n \ge 1$, $T \in \mathbb{N}$, and $0 < \eta \le 1$. Let $M^{(1)}, \dots, M^{(T)}$ be Hermitian $n\times n$ loss matrices with operator norm $\|M^{(t)}\| \le 1$. Run Algorithm 6 (MMWU) with $f_t(\rho) = \operatorname{Tr}(M^{(t)}\rho)$ and subgradients $G^{(t)} = M^{(t)}$, i.e.
--
--   $$
--   \rho^{(t)} = \frac{\exp\bigl(-\eta\sum_{\tau=1}^{t-1} M^{(\tau)}\bigr)}{\operatorname{Tr}\exp\bigl(-\eta\sum_{\tau=1}^{t-1} M^{(\tau)}\bigr)}, \qquad t = 1, \dots, T.
--   $$
--
--   Then each $\rho^{(t)}$ is a density matrix, and
--
--   $$
--   \operatorname{Tr}\Bigl(\sum_{t=1}^T M^{(t)}\rho^{(t)}\Bigr) \le \lambda_{\min}\Bigl(\sum_{t=1}^T M^{(t)}\Bigr) + \eta\,\operatorname{Tr}\Bigl(\sum_{t=1}^T (M^{(t)})^2\rho^{(t)}\Bigr) + \frac{\ln n}{\eta}.
--   $$
--
--   This regret bound is the engine of the MMWU semidefinite programming solver (Algorithm 7).
--
--   **Formalization Note** Traces of products of Hermitian matrices are real; their real parts are taken. $\lambda_{\min}$ is the smallest eigenvalue of the Hermitian sum, and $\|\cdot\|$ is the spectral (operator) norm.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 185, Theorem 8.10. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder


/-- Nannicini p.185, Theorem 8.10 (Thm. 3.1 in [Arora and Kale, 2016]). Let `n ≥ 1`,
`0 < η ≤ 1` (Alg. 6's input condition), and let `M^(1), …, M^(T)` be Hermitian `n × n` loss
matrices with operator norm `‖M^(t)‖ ≤ 1`. Running Alg. 6 with subgradients `G^(t) = M^(t)`, i.e.
`ρ^(t) = exp(−η Σ_{τ<t} M^(τ)) / Tr exp(−η Σ_{τ<t} M^(τ))`, produces density matrices
`ρ^(1), …, ρ^(T)` with
`Tr(Σ_t M^(t) ρ^(t)) ≤ λ_min(Σ_t M^(t)) + η Tr(Σ_t (M^(t))² ρ^(t)) + ln n / η` (8.11). -/
theorem mmwu_regret {n : ℕ} (hn : 0 < n) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (T : ℕ)
    (M : ℕ → Matrix (Fin n) (Fin n) ℂ) (hMherm : ∀ t ∈ Finset.Icc 1 T, (M t).IsHermitian)
    (hMnorm : ∀ t ∈ Finset.Icc 1 T, specNorm (M t) ≤ 1) :
    (∀ t ∈ Finset.Icc 1 T, IsDensityMatrix (mmwuIterate η M t)) ∧
      (∑ t ∈ Finset.Icc 1 T, M t * mmwuIterate η M t).trace.re ≤
        minEigenvalue (∑ t ∈ Finset.Icc 1 T, M t) +
          η * (∑ t ∈ Finset.Icc 1 T, M t ^ 2 * mmwuIterate η M t).trace.re +
          Real.log n / η := by
  sorry







end QAlgorithms.Nannicini
