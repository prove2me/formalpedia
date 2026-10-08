-- Prove2me | Theorems.Thm_StochApproxDyn_SubgaussianNoise_subgaussian_A1_ae
-- name    : StochApproxDyn.SubgaussianNoise.subgaussian_A1_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:49.405986+00:00
-- url     : https://prove2.me/theorems/eee949e0-9681-439e-8d1d-f495e02eb6e1
-- title:
--   Proposition 4.4 — subgaussian noise with $\sum_n e^{-c/\gamma_n}<\infty$ for all $c>0$ satisfies A1 almost surely
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a nondecreasing sequence $\{\mathcal F_n\}_{n\ge0}$ of sub-$\sigma$-algebras, let $F:\mathbb R^d\to\mathbb R^d$ be continuous, and let $\{\gamma_n\}_{n\ge1}$ be a deterministic step sequence ($\gamma_n\ge0$, $\sum_n\gamma_n=\infty$, $\gamma_n\to0$). Let $\{x_n\}$, given by
--   $$x_{n+1}-x_n=\gamma_{n+1}\big(F(x_n)+U_{n+1}\big),$$
--   be a Robbins–Monro algorithm: $U_n$ is $\mathcal F_n$-measurable and $E(U_{n+1}\mid\mathcal F_n)=0$. Suppose that:
--
--   1. $\{U_n\}$ is **subgaussian**: there is $\Gamma>0$ with $E(\exp\langle\theta,U_{n+1}\rangle\mid\mathcal F_n)\le\exp(\frac\Gamma2\|\theta\|^2)$ for all $n$ and all $\theta\in\mathbb R^d$;
--   2. for each $c>0$,
--   $$\sum_n e^{-c/\gamma_n}<\infty .$$
--
--   Then assumption A1 is satisfied with probability $1$: for $P$-almost every $\omega$, for every $T>0$,
--   $$\lim_{n\to\infty}\sup\Big\{\Big\|\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}(\omega)\Big\|:\ k=n+1,\dots,m(\tau_n+T)\Big\}=0
--   \quad\text{and}\quad \lim_{t\to\infty}\Delta(t,T)(\omega)=0,$$
--   where $\tau_n=\sum_{i\le n}\gamma_i$, $m(t)=\sup\{k:\tau_k\le t\}$ and $\Delta(t,T)=\sup_{0\le h\le T}\|\int_t^{t+h}\bar U(s)\,ds\|$.
--
--   Compared with Proposition 4.2 (bounded $q$-th moments and $\sum\gamma_n^{1+q/2}<\infty$), the stronger noise assumption allows step sizes that decrease much more slowly: the summability condition holds, for instance, whenever $\gamma_n\log n\to0$. Combined with Proposition 4.1, it shows that the interpolated process of such an algorithm is almost surely an asymptotic pseudotrajectory of the flow of $F$ when the remaining hypotheses of that proposition hold.
--
--   **Formalization Note** The term $e^{-c/\gamma_n}$ is read as $0$ when $\gamma_n=0$ (its limiting value $e^{-\infty}$); Lean's convention $c/0=0$ would otherwise make it $1$. The null set is the same for all $T>0$. Both forms of A1 that the paper calls equivalent are concluded. The second sentence of Proposition 4.4 (the asymptotic pseudotrajectory conclusion) is not part of this statement.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, p. 16 (PDF p. 17), Proposition 4.4, first conclusion; proof on p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.SubgaussianNoise

/-- Benaïm 1999, Proposition 4.4 (first conclusion), p. 16: let `{x_n}` given by (7) be a
Robbins–Monro algorithm. Suppose `{U_n}` is subgaussian and `{γ_n}` is a deterministic sequence
such that `∑_n e^{−c/γ_n} < ∞` for each `c > 0`. Then assumption A1 is satisfied with
probability 1: for `P`-almost every `ω`, the realised noise satisfies A1 for every `T > 0`, in
both of its stated forms.

The summability hypothesis is written with the term `e^{−c/γ_n}` read as `0` when `γ_n = 0`
(its value as a limit, `e^{−∞} = 0`); Lean's `c / 0 = 0` would otherwise turn it into `1`. -/
theorem subgaussian_A1_ae {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (hsg : IsSubgaussian P ℱ U)
    (hsum : ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => if 0 < γ (n + 1) then Real.exp (-c / γ (n + 1)) else 0)) :
    ∀ᵐ ω ∂P, StochApproxDyn.MartingaleNoise.IsA1 γ (fun n => U n ω) ∧ StochApproxDyn.MartingaleNoise.IsA1Delta γ (fun n => U n ω) := by sorry

end StochApproxDyn.SubgaussianNoise
