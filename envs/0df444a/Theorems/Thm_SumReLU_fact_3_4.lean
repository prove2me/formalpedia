-- Prove2me | Theorems.Thm_SumReLU_fact_3_4
-- name    : SumReLU.fact_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:24.037446+00:00
-- url     : https://prove2.me/theorems/789b2a71-f440-41d1-9610-5033e210922c
-- title:
--   Fact 3.4 — after $(\gamma,v)$-rejection sampling, $z=A^{-1/2}x_\gamma\sim N(0,I_d)$ and the label is $\sum\tilde\beta_i\sigma(\tilde w_i\cdot z)$
-- statement:
--   Fix a unit vector $v$ and $\gamma\in(0,1)$, and let $f(x)=\sum_{i=1}^k\beta_i\sigma(w_i\cdot x)$ with $\|w_i\|_2=1$, $\beta_i\in[0,1]$. Let $x_\gamma$ be $x\sim N(0,I_d)$ conditioned on acceptance by the rejection procedure with acceptance probability $a_{\gamma,v}(x)=\exp(-\tfrac{\gamma^{-2}-1}{2}(v\cdot x)^2)$, and $z=A^{-1/2}_{\gamma,v}x_\gamma$ with $A_{\gamma,v}=I_d-(1-\gamma^2)vv^\top$. Then:
--
--   1. $z\sim N(0,I_d)$;
--   2. the label $y_\gamma=f(x_\gamma)=f(A^{1/2}_{\gamma,v}z)$ satisfies, for every $z$,
--   $$
--   f(A^{1/2}_{\gamma,v}z)=\sum_{i=1}^k\tilde\beta_i\,\sigma(\tilde w_i\cdot z),\qquad \bar w_i=w_i^{\perp v}+\gamma(v\cdot w_i)v,\ \ \tilde w_i=\frac{\bar w_i}{\|\bar w_i\|_2},\ \ \tilde\beta_i=\beta_i\|\bar w_i\|_2\le\beta_i .
--   $$
--
--   So the localized data are again a Gaussian sum of $k$ ReLUs, which is what allows the coarse direction recovery procedure to be applied after rejection sampling.
--
--   **Formalization Note** The law of $x_\gamma$ is the Gaussian reweighted by $a_{\gamma,v}$ and normalized by its own mass; $A^{\pm1/2}_{\gamma,v}$ are the explicit rank-one updates $z\mapsto z-(1-\gamma)(v\cdot z)v$ and $x\mapsto x+(\gamma^{-1}-1)(v\cdot x)v$.
--
--   Differences from the source:
--   - encoding: $z\sim N(0,I_d)$ for $z=A^{-1/2}_{\gamma,v}x_\gamma$, $x_\gamma$ the accepted sample → the pushforward of the normalized reweighted Gaussian `acceptedLaw γ v` under the map $A^{-1/2}_{\gamma,v}$ is `stdGaussian`; reason: Lean has no conditioned random variable; the accepted sample's law is the normalized reweighting, and the statement is about that law
--   - encoding: $\mathbb E[y_\gamma\mid z]=\sum_i\tilde\beta_i\sigma(\tilde w_i\cdot z)$ → for every $z$: $f(A^{1/2}_{\gamma,v}z)=\sum_i\tilde\beta_i\sigma(\tilde w_i\cdot z)$; reason: $y_\gamma=f(x_\gamma)$ and $x_\gamma=A^{1/2}_{\gamma,v}z$, so $y_\gamma$ is this function of $z$ and equals its conditional expectation; the pointwise identity avoids conditional expectations, which are defined only almost everywhere
--   - encoding: $A^{\pm1/2}_{\gamma,v}$ → the rank-one updates $z-(1-\gamma)(v\cdot z)v$ and $x+(\gamma^{-1}-1)(v\cdot x)v$; reason: these are the symmetric square root of $A_{\gamma,v}$ and its inverse for unit $v$ and $\gamma>0$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Fact 3.4, p.13 (PDF p.15); proof pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_rejection

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Fact 3.4** (Properties of Rejection Sampling).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Fact 3.4, p.13 (PDF p.15); proof p.13–14 (PDF pp.15–16): "Fix parameters v ∈ S^{d−1} and
γ ∈ (0, 1). Let (x, y) ∼ D be such that x ∼ N(0, I_d) and y(x) = ∑_{i=1}^k β_i σ(w_i · x) with
‖w_i‖₂ = 1 and β_i ∈ [0, 1] for i ∈ [k]. Let (x_γ, y_γ) be the sample accepted by RS_{γ,v}. Let
z := A_{γ,v}^{−1/2} x_γ, where A_{γ,v} := I_d − (1 − γ²)vvᵀ. Then, the following statements both hold:
1. z follows the standard normal distribution, i.e., z ∼ N(0, I_d). 2. E[y_γ | z] = ∑_{i=1}^k
β̃_i σ(w̃_i · z), where w̄_i = w_i^{⊥v} + γ(v · w_i)v, w̃_i = w̄_i/‖w̄_i‖₂, and β̃_i = β_i‖w̄_i‖₂ ≤ β_i."

**Formalization Note.**
* Item 1: the law of `x_γ` is `acceptedLaw γ v` (`N(0, I_d)` reweighted by `a_{γ,v}` and normalized);
  its pushforward under the explicit rank-one map `A_{γ,v}^{−1/2}` is `N(0, I_d)`.
* Item 2: `y_γ = f(x_γ)` and `x_γ = A_{γ,v}^{1/2} z`, so `y_γ` is the function `z ↦ f(A_{γ,v}^{1/2} z)`
  of `z` and `E[y_γ | z]` is that function. It is stated pointwise for every `z` (no conditional
  expectation, which is defined only almost everywhere). -/
theorem fact_3_4 {d k : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) (hf : InClass β w) :
    (acceptedLaw γ v).map (Ainvhalf γ v) = stdGaussian (EuclideanSpace ℝ (Fin d)) ∧
      (∀ z : EuclideanSpace ℝ (Fin d),
        reluSum β w (Ahalf γ v z) = ∑ i, btilde (β i) γ v (w i) * relu (inner ℝ (wtilde γ v (w i)) z)) ∧
      ∀ i, btilde (β i) γ v (w i) ≤ β i := by sorry

end SumReLU
