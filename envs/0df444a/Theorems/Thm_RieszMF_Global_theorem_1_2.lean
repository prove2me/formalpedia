-- Prove2me | Theorems.Thm_RieszMF_Global_theorem_1_2
-- name    : RieszMF.Global.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:43.380622+00:00
-- url     : https://prove2.me/theorems/6e0a0ef1-2a08-488a-9c15-b6825d5623e5
-- title:
--   Theorem 1.2, p. 7 ($0<s<d-2$) — $\mathbb E|F_N(x^t_N,\mu^t)|\le C(|F_N(x^0_N,\mu^0)|+C_pN^{-\beta_p})$ uniformly in $t\ge0$
-- statement:
--   Let $d\ge3$, $0<s<d-2$, $\sigma>0$, let $\mathbb M$ satisfy $\mathbb M\xi\cdot\xi\le0$ and let $\mathsf g$ be an admissible potential which is globally superharmonic ($\Delta\mathsf g\le0$ on $\mathbb R^d\setminus\{0\}$, and, when $d-4<s$, assumption (viii) holds with (1.15)–(1.16) on all of $\mathbb R^{d+m}$). Let $x_N$ be the solution of the particle system (1.1) from pairwise distinct initial positions $x^0_N$, driven by $N$ independent standard Brownian motions, and let $\mu\in C([0,\infty);\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d))$ be the solution of the mean-field equation (1.5).
--
--   There are exponents $\beta_p>0$ depending only on $s,d,p$, a constant $C>0$ depending only on $s,d,\sigma,\mathbb M,\mathsf g$ and $\|\mu^0\|_{L^\infty}$, and, for every $d/(s+2)<p\le\infty$, a constant $C_p>0$ and a threshold $N_0$ such that for all $t\ge0$ and all $N\ge N_0$,
--
--   $$\mathbb E\big(|F_N(x^t_N,\mu^t)|\big)\le C\big(|F_N(x^0_N,\mu^0)|+C_pN^{-\beta_p}\big).$$
--
--   The bound is uniform in time: if the initial modulated energy vanishes as $N\to\infty$, the empirical measure of the particles stays close to the mean-field solution for all times at a rate independent of $t$.
--
--   **Formalization Note** The paper states (1.19) for $0\le s<d-2$ with the factor $1+(t^{1/\sigma}\log(1+t))\mathbf 1_{s=0}$; only the case $0<s<d-2$ is posed here, where that factor is $1$ and is omitted. For $s=0$ the proof (7.15) gives a factor of order $t^{C/\sigma}$ instead, so the printed $s=0$ clause is not stated. The constant $C$ precedes $p$ because the page lists no dependence of $C$ on $p$; $N_0$ may also depend on $s,d,\sigma,\mathbb M,\mathsf g,p$. The expectation is the lower Lebesgue integral of $|F_N|$, so no integrability is assumed.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 7, Theorem 1.2, (1.19); assumptions of Theorem 1.1, p. 6

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Theorem 1.2 (p. 7), case `0 < s < d - 2`: under the assumptions of Theorem 1.1 and global
superharmonicity (`r₀ = ∞` in (iii), and in (1.15)–(1.16) of (viii)), there are exponents
`β_p > 0` depending on `s, d, p`, a constant `C > 0` depending on `s, d, σ, 𝕄, g, ‖μ^0‖_{L^∞}`,
and for every `d/(s+2) < p ≤ ∞` constants `C_p > 0`, `N₀` such that, for all `t ≥ 0` and all
`N ≥ N₀`, `𝔼|F_N(x^t_N, μ^t)| ≤ C (|F_N(x^0_N, μ^0)| + C_p N^{-β_p})`. -/
theorem theorem_1_2 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 < s → s < (d : ℝ) - 2 →
    ∃ β : ℝ≥0∞ → ℝ, (∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (s + 2)) < p → 0 < β p) ∧
    ∀ (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ),
      0 < σ → RieszMF.Linear.NegSemidef M → Admissible d s M g r₀ → GloballySuperharmonic g →
      ((d : ℝ) - 4 < s → HasExtensionGlobal d s g) →
    ∀ L : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (s + 2)) < p →
    ∃ Cp : ℝ, 0 < Cp ∧ ∃ N₀ : ℕ,
    ∀ (μ0 : RieszMF.Linear.E d → ℝ) (μ : ℝ≥0 → RieszMF.Linear.E d → ℝ),
      supNorm μ0 = L → IsMildSolution d σ M g μ0 μ → RieszMF.Linear.IsProbPath μ →
    ∀ N : ℕ, N₀ ≤ N → 0 < N →
    ∀ x0 : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x0 i ≠ x0 j) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d) (x : Fin N → ℝ≥0 → Ω → RieszMF.Linear.E d),
      IsBrownianFamily P W → IsParticleSolution P σ M g x0 W x →
    ∀ t : ℝ≥0,
      ∫⁻ ϖ, ENNReal.ofReal |RieszMF.Linear.modEnergy N g (fun i => x i t ϖ) (μ t)| ∂P ≤
        ENNReal.ofReal (C * (|RieszMF.Linear.modEnergy N g x0 μ0| + Cp * (N : ℝ) ^ (-β p))) := by sorry

end RieszMF.Global
