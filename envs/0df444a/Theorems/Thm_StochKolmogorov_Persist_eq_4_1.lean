-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_eq_4_1
-- name    : StochKolmogorov.Persist.eq_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:17.969013+00:00
-- url     : https://prove2.me/theorems/986b9ae0-ab14-444a-95d5-570e1af49dfe
-- title:
--   (4.1), §4, p. 16 — Assumption 1.2 gives p ∈ ℝⁿ,◦₊ with ‖p‖ = δ₀ and min over μ ∈ M of Σᵢ pᵢλᵢ(μ) = 2ρ* > 0
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Suppose Assumption 1.2 holds and let $\delta_0>0$.
--
--   There exist $p=(p_1,\dots,p_n)\in\mathbb R^{n,\circ}_+$ with $\|p\|=\sum_ip_i=\delta_0$ and $\rho^*>0$ such that
--   $$\min_{\mu\in\mathcal M}\sum_ip_i\lambda_i(\mu)=2\rho^*>0.$$
--   Thus every boundary ergodic measure has weighted invasion rate at least $2\rho^*$, and one attains it.
--
--   This is the direction of the minimax equivalence of [SBA11, Lemma 4] that the paper uses: a single positive weighting of the species makes the weighted invasion rate uniformly positive on every boundary ergodic measure. It fixes $p$ and $\rho^*$ in the Lyapunov function $V$ of (3.4) for the rest of §4.
--
--   **Formalization Note** The paper writes $\min_{\mu\in\mathcal M}\{\sum_ip_i\lambda_i(\mu)\}:=2\rho^*>0$; the statement records both the lower bound and an attaining boundary ergodic measure. Only the implication Assumption 1.2 $\Rightarrow$ (4.1) is stated. The normalization $\|p\|=\delta_0$ is the paper's "by rescaling if necessary". The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, (4.1), §4, p. 16 (citing [SBA11, Lemma 4])

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- (4.1), §4, p. 16 (cited from [SBA11, Lemma 4]), the direction used: Assumption 1.2 gives
`p ∈ ℝⁿ,◦₊`, rescaled to `‖p‖ = δ₀`, and `ρ* > 0` with `min_{μ∈M} ∑ᵢ pᵢλᵢ(μ) = 2ρ*`, including attainment. -/
theorem eq_4_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ p ∈ openOrthant n, l1 p = δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧
      IsWeightedInvasionMin P C X p ρ := by sorry

end StochKolmogorov.Persist
