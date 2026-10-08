-- Prove2me | Theorems.Thm_TamedEuler_Convergence_theorem_1_1
-- name    : TamedEuler.Convergence.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:37.968978+00:00
-- url     : https://prove2.me/theorems/69ae0bb3-933b-4cc1-aa31-f9395f1f592e
-- title:
--   Theorem 1.1 (Main result), p. 5 — (𝔼 sup_{t≤T} ‖X_t − Ȳ^N_t‖^p)^{1/p} ≤ C_p N^{−1/2}
-- statement:
--   Assume the standing setting of p. 2: $T>0$; a probability space with a normal filtration $(\mathcal F_t)$; an $m$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$; an $\mathcal F_0$-measurable initial value $\xi$ with $\mathbb E\|\xi\|^p<\infty$ for all $p\ge1$; a continuously differentiable drift $\mu:\mathbb R^d\to\mathbb R^d$ and a diffusion $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$ with one constant $c>0$ such that
--   $$\|\mu'(x)\|\le c(1+\|x\|^c),\quad \|\sigma(x)-\sigma(y)\|\le c\|x-y\|,\quad \langle x-y,\mu(x)-\mu(y)\rangle\le c\|x-y\|^2 .$$
--   Let $X$ be a solution of the SDE $dX_t=\mu(X_t)\,dt+\sigma(X_t)\,dW_t$, $X_0=\xi$, on $[0,T]$, i.e. an adapted process with continuous paths satisfying (2), and let $\bar Y^N$ be the interpolations (10) of the tamed Euler approximations (8). Then there is a family $C_p\in[0,\infty)$, $p\in[1,\infty)$, such that
--   $$\Big(\mathbb E\Big[\sup_{t\in[0,T]}\|X_t-\bar Y^N_t\|^p\Big]\Big)^{1/p}\le C_p\cdot N^{-1/2}$$
--   for all $N\in\mathbb N$ and all $p\in[1,\infty)$.
--
--   The tamed Euler scheme, an explicit method that costs the same as the Euler–Maruyama scheme, thus converges strongly with the standard order $\tfrac12$, uniformly in time and in every $L^p$, for SDEs with one-sided Lipschitz, superlinearly growing drift, where the explicit Euler scheme diverges.
--
--   **Formalization Note** $X$ is any process satisfying the published `IsSolution` relation (existence and uniqueness are cited in the paper, not part of the claim); $\sigma$ is passed to it entrywise. The filtration is right-continuous and solutions are adapted to its $\mathbb P$-completion; $W$ is defined on $[0,\infty)$. The constants $C_p$ are chosen before $N$ and may depend on everything except $N$. The expectation of the supremum is a $[0,\infty]$-valued integral. All matrix norms are operator norms.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 5, Theorem 1.1, (11)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 5, Theorem 1.1 (Main result), (11):
in the standing setting, for every solution `X` of the SDE (2) driven by `W`, there is a
family `C_p ∈ [0, ∞)`, `p ∈ [1, ∞)`, with
`(𝔼[sup_{t ∈ [0,T]} ‖X_t − Ȳ^N_t‖^p])^{1/p} ≤ C_p · N^{−1/2}` for all `N ∈ ℕ`, `p ∈ [1, ∞)`,
where `Ȳ^N` is the interpolation (10) of the tamed Euler scheme (8). Expectation and
supremum are taken in `[0, ∞]`. -/
theorem theorem_1_1 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ)
    (X : ℝ≥0 → Ω → SDEState d)
    (hX : SabanisEuler.Shared.IsSolution P ℱ W T ξ (fun z => mu z.2)
      (fun z => toDiffusion (σ z.2)) X) :
    ∃ C : ℝ → ℝ, ∀ p : ℝ, 1 ≤ p → 0 ≤ C p ∧ ∀ N : ℕ, 1 ≤ N →
      (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ‖X t ω - Ybar T mu σ ξ W N t ω‖ₑ) ^ p ∂P) ^ (1 / p)
        ≤ ENNReal.ofReal (C p * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end TamedEuler.Convergence
