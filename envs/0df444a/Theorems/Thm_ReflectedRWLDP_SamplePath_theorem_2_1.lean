-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_theorem_2_1
-- name    : ReflectedRWLDP.SamplePath.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:14.599446+00:00
-- url     : https://prove2.me/theorems/3b637a0f-e77e-4999-b7dd-59dde66ae43a
-- title:
--   Theorem 2.1 — sample-path LDP for $\bar Y_n=\frac1n\sum_{i\le\lfloor n\cdot\rfloor}X_i^p$ in $(\mathbb D[0,1],\mathcal T_{M_1'})$ at speed $n^\alpha$
-- statement:
--   Let $U_1,U_2,\dots$ be i.i.d. copies of a random variable $U$ with $\mathbf E(U)<0$ satisfying Assumptions 2.1–2.3: $-\infty\le\theta_-<0<\theta_+\le\infty$ for the endpoints of $\{\theta:\mathbf E e^{\theta U}<\infty\}$; $\log\mathbf P(U\ge n)/n\to-\theta_+$ and $\log\mathbf P(-U\ge n)/n\to\theta_-$; and $\mathbf P(U>0)>0$. Let $X_{n+1}=[X_n+U_{n+1}]^+$, $X_0=0$, be the reflected random walk. Fix $p>0$, let $\alpha=1/(1+p)$, and let
--   $$\bar Y_n(t)=\frac1n\sum_{i=1}^{\lfloor nt\rfloor}X_i^p,\qquad t\in[0,1].$$
--   Then $\bar Y_n$ satisfies a large deviation principle in $(\mathbb D[0,1],\mathcal T_{M_1'})$ with speed $n^\alpha$ and rate function
--   $$I_Y(\zeta)=\begin{cases}\mathcal B^*_0\sum_{t:\zeta(t)\ne\zeta(t-)}(\zeta(t)-\zeta(t-))^\alpha&\text{if }\zeta\in\mathbb D^{(\lambda)}[0,1],\\ \infty&\text{otherwise.}\end{cases}$$
--   That is, for every open $G$ and every closed $F$,
--   $$-\inf_{\xi\in G}I_Y(\xi)\le\liminf_{n\to\infty}\frac{\log\mathbf P(\bar Y_n\in G)}{n^\alpha},\qquad \limsup_{n\to\infty}\frac{\log\mathbf P(\bar Y_n\in F)}{n^\alpha}\le-\inf_{\xi\in F}I_Y(\xi).$$
--   Here $\lambda=\mathbf E(\sum_{i=1}^{T_1}X_i^p)/\mathbf E(T_1)$ is the long-run mean of $X^p$, $\mathbb D^{(\lambda)}[0,1]$ is the set of paths $\lambda t+\zeta(t)$ with $\zeta$ a non-decreasing pure jump path with $\zeta(0)\ge0$, and $\mathcal B^*_0$ is the value of the variational problem $(\mathcal B_0)$.
--
--   A large deviation of the additive functional $\sum X_i^p$ is produced by a countable number of extreme busy periods, each costing $\mathcal B^*_0$ times its area to the power $\alpha$.
--
--   **Formalization Note** The paper states the theorem on $\mathbb D[0,T]$ but defines $\bar Y_n$ on $[0,1]$ and proves it with $T=1$ (p. 9); the formalization takes $T=1$. The bounds for open and closed sets are the standard equivalent of (2.2), "for any measurable set $A$". Jumps in $I_Y$ use $\zeta(0-)=0$, so a jump at time $0$ counts. $I_Y$ takes values in $[0,\infty]$; the paper writes its codomain as $\mathbb R_+$.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 6, Theorem 2.1, (2.1)–(2.2); T = 1 as on p. 9

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath

/-- **Theorem 2.1** (p. 6), with `T = 1`. Under the standing assumptions (i.i.d. increments with
`E U < 0`, Assumptions 2.1–2.3, `p > 0`), `Ȳ_n(t) = (1/n) ∑_{i=1}^{⌊nt⌋} X_i^p` satisfies the large deviation
principle in `(𝔻[0,1], 𝒯_{M₁′})` with speed `n^α`, `α = 1/(1+p)`, and rate function
`I_Y(ζ) = B*₀ ∑_{t : ζ(t) ≠ ζ(t−)} (ζ(t) − ζ(t−))^α` on `𝔻^{(λ)}[0,1]`, `∞` elsewhere. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    SatisfiesLDP P (Ybar U p) dM1 (fun n => (n : ℝ) ^ alpha p) (rateY P U p) := by sorry

end ReflectedRWLDP.SamplePath
