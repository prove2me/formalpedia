-- Prove2me | Theorems.Thm_SumReLU_eq_4
-- name    : SumReLU.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:53.222187+00:00
-- url     : https://prove2.me/theorems/c66fb699-f64f-4328-9f55-468df057f297
-- title:
--   Eq. (4) — $\hat\sigma_p^{-1}\mathbb E[y\,\mathrm{he}_p(v\cdot x)]=\sum_i\beta_i\cos^p\theta_\pm(v,w_i)$ for even $p$
-- statement:
--   Let $f(x)=\sum_{i=1}^k\beta_i\sigma(w_i\cdot x)$ with $\beta_i\in[0,1]$ and $\|w_i\|_2=1$, let $v$ be a unit vector and let $p$ be an even integer. With $x\sim N(0,I_d)$ and $y=f(x)$,
--   $$
--   a_p(v):=\frac{1}{\hat\sigma_p}\,\mathbb E\big[y\,\mathrm{he}_p(v\cdot x)\big]=\sum_{i=1}^k\beta_i\cos^p\theta_\pm(v,w_i),
--   $$
--   where $\mathrm{he}_p$ is the normalized probabilists' Hermite polynomial and $\hat\sigma_p$ the $p$-th Hermite coefficient of the ReLU. Equivalently $a_p(v)=\sum_i\beta_i|v\cdot w_i|^p$.
--
--   The left side can be estimated from samples; the right side is large exactly when $v$ is close to a heavy hidden vector. This identity drives the closeness tester of the algorithm.
--
--   Differences from the source:
--   - encoding: $\mathbb E[y\,\mathrm{he}_p(v\cdot x)]$ over $(x,y)\sim D$ → $\int f(x)\,\mathrm{he}_p(v\cdot x)\,dN(x)$; reason: $y=f(x)$ and $x\sim N(0,I_d)$
--   - reading: "for even integer $p$", $v$ a candidate direction → every even $p\in\mathbb N$ (including $0$) and every unit vector $v$; reason: $p$ is a Hermite degree, hence nonnegative; $v$ is a unit vector wherever $a_p(v)$ is used (the tester's candidates), and the identity needs $\|v\|_2=1$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Eq. (4), §1.2.2, p.6 (PDF p.8); restated p.17 (PDF p.19)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_thetaPM
import Definitions.Def_SumReLU_reluHermite

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Eq. (4)**: the degree-`p` moment identity behind the closeness tester.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), §1.2.2, p.6 (PDF p.8), Eq. (4): "for even integer p, we have the following identity:
a_p(v) := (1/σ̂_p) E[y he_p(v · x)] = ∑_i β_i cos^p θ±(v, w_i)"; restated p.17 (PDF p.19) as
`∑_i β_i |v · w_i|^p` and used in the proof of Lemma 3.8, p.17.

**Formalization Note.** `(x, y) ∼ D` with `x ∼ N(0, I_d)` and `y = f(x)`, so
`E[y he_p(v · x)] = E_{x∼N(0,I_d)}[f(x) he_p(v · x)]`. `v` is a unit vector (as in the tester).
Every even `p ≥ 0` is covered (`σ̂_p ≠ 0` for even `p`). -/
theorem eq_4 {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) (hf : InClass β w)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (p : ℕ) (hp : Even p) :
    (reluHermite p)⁻¹ * ∫ x, reluSum β w x * GaussPart.hermiteOne p (inner ℝ v x)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∑ i, β i * Real.cos (thetaPM v (w i)) ^ p := by sorry

end SumReLU
