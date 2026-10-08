-- Prove2me | Theorems.Thm_SAARate_SharpLD_failure_subset_exists_nonpos
-- name    : SAARate.SharpLD.failure_subset_exists_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:51.931994+00:00
-- url     : https://prove2.me/theorems/671f122b-2c3d-440a-8070-abee0de2eefd
-- title:
--   Proof of Theorem 3.1, p. 11 — if f̂′_N(x̄,·) > 0 on T_Θ(x̄)∩S^{m−1} then A_N = {x̄}; hence P(ℰ^c_N) ≤ P(ζ_N ∈ F)
-- statement:
--   Let $h:\mathbb R^m\times\Omega\to\mathbb R$ with $h(\cdot,\omega)$ convex for every $\omega$, let $\Theta\subseteq\mathbb R^m$ be convex and $\bar x\in\Theta$. Write $T_\Theta(\bar x)$ for the tangent cone of $\Theta$ at $\bar x$ and $S^{m-1}$ for the unit sphere.
--
--   1. For every sample path $s=(s_0,s_1,\dots)$ in $\Omega$ and every $N$, if the SAA objective $\hat f_N(x)=N^{-1}\sum_{j<N}h(x,s_j)$ satisfies
--   $$\hat f_N'(\bar x,d)>0\qquad\text{for all } d\in T_\Theta(\bar x)\cap S^{m-1},$$
--   then $\bar x$ is the unique minimizer of $\hat f_N$ over $\Theta$: $A_N=\{\bar x\}$.
--   2. Consequently, for any measure $Q$ on a sample space $S$ and any maps $\omega_j:S\to\Omega$, and every $N$,
--   $$Q\bigl(A_N\neq\{\bar x\}\bigr)\le Q\bigl(\exists\, d\in T_\Theta(\bar x)\cap S^{m-1}:\ \hat f_N'(\bar x,d)\le0\bigr).$$
--
--   The event on the left is $\mathcal E_N^c$ of (3.7); the event on the right is $\{\zeta_N\in F\}$ with $\zeta_N=\hat f'_N(\bar x,\cdot)$ and $F$ of (3.9). This reduces Theorem 3.1 to a large deviation bound for $\zeta_N$.
--
--   **Formalization Note** "$\zeta_N\in F$", i.e. $\inf_{d\in T_\Theta(\bar x)\cap S^{m-1}}\zeta_N(d)\le0$, is written as "some $d$ has $\zeta_N(d)\le0$": $\zeta_N$ is continuous and $T_\Theta(\bar x)\cap S^{m-1}$ compact, so the infimum is attained, and if the set is empty both events are empty. The probabilistic structure is not needed for the inclusion, so $Q$ is an arbitrary measure (outer measure on possibly non-measurable events); closedness of $\Theta$ is dropped. Both changes make the statement more general.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 11, proof of Theorem 3.1, (3.7), (3.9), the inequality P(ℰ^c_N) ≤ P(ζ_N ∈ F)

import Mathlib
import Definitions.Def_SAARate_SharpLD_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace SAARate.SharpLD

theorem failure_subset_exists_nonpos {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (h : SAARate.Sharp.E m → Ω → ℝ) (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (Θ : Set (SAARate.Sharp.E m)) (hΘv : Convex ℝ Θ) (xbar : SAARate.Sharp.E m) (hx : xbar ∈ Θ)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) (ω : ℕ → S → Ω) :
    (∀ (s : ℕ → Ω) (N : ℕ),
      (∀ d ∈ tangentConeAt ℝ Θ xbar ∩ Metric.sphere (0 : SAARate.Sharp.E m) 1,
          0 < SAARate.Sharp.dirDeriv (SAARate.Sharp.saaObj h s N) xbar d) →
        SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ = {xbar}) ∧
    ∀ N : ℕ,
      Q {s | SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ ≠ {xbar}} ≤
        Q {s | ∃ d ∈ tangentConeAt ℝ Θ xbar ∩ Metric.sphere (0 : SAARate.Sharp.E m) 1,
          SAARate.Sharp.dirDeriv (SAARate.Sharp.saaObj h (fun j => ω j s) N) xbar d ≤ 0} := by sorry

end SAARate.SharpLD
