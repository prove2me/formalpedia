-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_mirrorDescent_maxCut_converges
-- name    : QAlgorithms.Nannicini.mirrorDescent_maxCut_converges
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:20.65587+00:00
-- url     : https://prove2.me/theorems/08e42fae-7c99-496d-b650-0b36223b9dc0
-- title:
--   Convergence of inexact entropic mirror descent for the MaxCut SDP feasibility problem
-- statement:
--   Let $n\ge2$, let $C\in\mathbb R^{n\times n}$ be a nonzero symmetric matrix, $\hat C=C/\|C\|_F$, $\gamma\in[-1,1]$, $\epsilon>0$, and let $f_\gamma(\rho)=\max\{\gamma-\operatorname{Tr}(\hat C\rho),\sum_j|\rho_{jj}-1/n|\}$. Suppose some density matrix $\rho^*$ satisfies $f_\gamma(\rho^*)=0$. Set
--
--   $$\eta=\frac{\epsilon}{16},\qquad T=\Big\lceil\frac{64}{\epsilon^2}\log_2 n\Big\rceil,$$
--
--   and run Alg. 6: $\rho^{(t)}=\exp\big(-\eta\sum_{\tau<t}G^{(\tau)}\big)/\operatorname{Tr}\exp\big(-\eta\sum_{\tau<t}G^{(\tau)}\big)$ for $t=1,\dots,T$, where for each $t=1,\dots,T-1$ the matrix $G^{(t)}$ is Hermitian and an $\epsilon/2$-subgradient of $f_\gamma$ at $\rho^{(t)}$ over the space of Hermitian matrices: $f_\gamma(X)\ge f_\gamma(\rho^{(t)})+\operatorname{Re}\operatorname{Tr}(G^{(t)}(X-\rho^{(t)})^\dagger)-\epsilon/2$ for every Hermitian $X$. Then $\rho^{(1)},\dots,\rho^{(T)}$ are density matrices and
--
--   $$f_\gamma\Big(\frac1T\sum_{t=1}^{T}\rho^{(t)}\Big)\le\epsilon.$$
--
--   This is the convergence guarantee behind the quantum MaxCut SDP solver: each step needs only a classical description of an approximate subgradient.
--
--   **Formalization Note** The printed $T=(64/\epsilon^2)\log n$ is replaced by its ceiling (a larger $T$ only helps), $\log$ is base 2 (the book's convention), and $n\ge2$ is added: at $n=1$, $T=0$ and the empty average is the zero matrix, where $f_\gamma(0)=\max(\gamma,1)>\epsilon$ for $\epsilon<1$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 202, Theorem 8.30. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP



/-- Nannicini p.202, Theorem 8.30 (Convergence of mirror descent for MaxCut SDP). Suppose there
exists `ρ* ∈ S^n_{+,1}` such that `f_γ(ρ*) = 0`. Then the mirror descent algorithm Alg. 6 with step
size `η = ϵ/16`, inexact subgradients `G^(t) ∈ ∂_{ϵ/2} f_γ(ρ^(t))`, and number of steps
`T = (64/ϵ²) log n`, returns density matrices `ρ^(1), …, ρ^(T)` such that
`f_γ((1/T) Σ_{t=1}^T ρ^(t)) ≤ ϵ`.

Alg. 6 obtains `G^(t)` for `t = 1, …, T − 1` and returns `ρ^(1), …, ρ^(T)`, `ρ^(t)` being
`mmwuIterate η G t`; each `G^(t)` is a Hermitian matrix (an element of the dual of the space of
Hermitian matrices) and an `ϵ/2`-subgradient of `f_γ` at `ρ^(t)` over all Hermitian matrices.
Two recorded adjustments: `T = ⌈(64/ϵ²) log₂ n⌉` (the printed `T` need not be an integer; the
ceiling only enlarges it), and `n ≥ 2` (at `n = 1`, `log n = 0` gives `T = 0` and the average of
no iterates is `0`, with `f_γ(0) = max(γ, 1) > ϵ` for `ϵ < 1`). -/
theorem mirrorDescent_maxCut_converges {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∃ ρs : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix ρs ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρs = 0)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hG : ∀ t, 1 ≤ t → t < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      (G t).IsHermitian ∧
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) (mmwuIterate (ε * 16⁻¹) G t)
          (traceRePairing (G t))) :
    (∀ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊,
        IsDensityMatrix (mmwuIterate (ε * 16⁻¹) G t)) ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ
        (((⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ : ℕ) : ℂ)⁻¹ •
          ∑ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊, mmwuIterate (ε * 16⁻¹) G t) ≤ ε := by
  sorry


















end QAlgorithms.Nannicini
