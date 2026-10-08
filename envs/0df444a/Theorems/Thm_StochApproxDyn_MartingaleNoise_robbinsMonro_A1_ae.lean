-- Prove2me | Theorems.Thm_StochApproxDyn_MartingaleNoise_robbinsMonro_A1_ae
-- name    : StochApproxDyn.MartingaleNoise.robbinsMonro_A1_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:28:58.642982+00:00
-- url     : https://prove2.me/theorems/d6aa6b11-341a-403a-9ece-34dc3d504393
-- title:
--   Proposition 4.2: martingale noise with bounded $q$-th moments and $\sum\gamma_n^{1+q/2}<\infty$ satisfies A1 almost surely
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a nondecreasing sequence $\{\mathcal F_n\}$ of sub-$\sigma$-algebras, $F:\mathbb R^d\to\mathbb R^d$ continuous, and $\{\gamma_n\}$ a deterministic step sequence ($\gamma_n\ge0$, $\sum\gamma_n=\infty$, $\gamma_n\to0$). Let $\{x_n\}$, given by
--   $$x_{n+1}-x_n=\gamma_{n+1}\big(F(x_n)+U_{n+1}\big),$$
--   be a Robbins–Monro algorithm: $U_n$ is $\mathcal F_n$-measurable and $E(U_{n+1}\mid\mathcal F_n)=0$. Suppose that for some $q\ge2$
--   $$\sup_nE\big(\|U_{n+1}\|^q\big)<\infty\qquad\text{and}\qquad\sum_n\gamma_n^{1+q/2}<\infty .$$
--   Then assumption A1 holds with probability $1$: for $P$-almost every $\omega$, for every $T>0$,
--   $$\lim_{n\to\infty}\sup\Big\{\Big\|\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}(\omega)\Big\|:\ k=n+1,\dots,m(\tau_n+T)\Big\}=0\qquad\text{and}\qquad\lim_{t\to\infty}\Delta_\omega(t,T)=0,$$
--   where $\Delta_\omega(t,T)=\sup_{0\le h\le T}\|\int_t^{t+h}\bar U_\omega(s)\,ds\|$.
--
--   Combined with Proposition 4.1, this shows that the interpolated process of a Robbins–Monro algorithm with bounded iterates is almost surely an asymptotic pseudotrajectory of the flow of $F$.
--
--   **Formalization Note** The exceptional null set is chosen once for all $T>0$ (the almost-sure quantifier is outside "for all $T$"). Both forms of A1 that the paper calls equivalent are concluded. The moment hypothesis is a uniform bound on integrals in $[0,\infty]$; it implies integrability of every $U_{n+1}$, which the Robbins–Monro definition also requires. $q$ is a real number, powers are real powers of nonnegative numbers, and $\gamma_0$, $U_0$ are unused.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, p. 15 (PDF p. 16), Proposition 4.2

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, Proposition 4.2, p. 15: let `{x_n}` given by (7) be a Robbins–Monro algorithm.
Suppose that for some `q ≥ 2`, `sup_n E(‖U_{n+1}‖^q) < ∞` and `∑_n γ_n^{1+q/2} < ∞`. Then
assumption A1 holds with probability 1: for `P`-almost every `ω`, the realised noise
sequence satisfies A1 for every `T > 0` (in both of its stated forms). -/
theorem robbinsMonro_A1_ae {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (q : ℝ) (hq : 2 ≤ q)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n : ℕ, ∫⁻ ω, ‖U (n + 1) ω‖ₑ ^ q ∂P ≤ M)
    (hsum : Summable (fun n : ℕ => γ (n + 1) ^ (1 + q / 2))) :
    ∀ᵐ ω ∂P, IsA1 γ (fun n => U n ω) ∧ IsA1Delta γ (fun n => U n ω) := by sorry

end StochApproxDyn.MartingaleNoise
