-- Prove2me | Theorems.Thm_StabGen_Entropy_entropy_regularization_uniform_stability
-- name    : StabGen.Entropy.entropy_regularization_uniform_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:12:27.656391+00:00
-- url     : https://prove2.me/theorems/3f328926-5aad-43c7-8ed5-c78128b4b8dd
-- title:
--   Theorem 24 — relative-entropy regularization has uniform stability $M^2/(\lambda m)$
-- statement:
--   Let $\Theta$ be a measurable space with a σ-finite reference measure $\nu$, and let $F$ be the set of probability densities with respect to $\nu$. Let $r$ be a loss on the base class $\{h_\theta:\theta\in\Theta\}$, measurable in $\theta$ and bounded by $M$: $0\le r(h_\theta,z)\le M$ for all $\theta,z$. Let $\ell(g,z)=\int_\Theta r(h_\theta,z)g(\theta)\,d\theta$ be the averaged loss (28), let $f_0\in F$ be fixed, and let $\lambda>0$. For a training set $S=(z_1,\dots,z_m)$, let $f\in F$ minimize
--   $$R_r(g)=\frac1m\sum_{j=1}^m\ell(g,z_j)+\lambda K(g,f_0)\qquad(29)$$
--   over $F$, where $K$ is the relative entropy, and for an index $i$ let $f^{\setminus i}\in F$ minimize $R_r^{\setminus i}(g)=\frac1m\sum_{j\ne i}\ell(g,z_j)+\lambda K(g,f_0)$ over $F$. Then for every $z$,
--   $$|\ell(f,z)-\ell(f^{\setminus i},z)|\le\frac{M^2}{\lambda m} .$$
--
--   In the paper's terms, the learning algorithm $A_S=\arg\min_{g\in F}R_r(g)$ has uniform stability $\beta\le M^2/(\lambda m)$ with respect to $\ell$. With Theorem 12 of the paper this yields exponential generalization bounds for maximum-a-posteriori style mixtures regularized by the relative entropy to a prior.
--
--   **Formalization Note** The statement is the pairwise form the paper's proof establishes: $f^{\setminus i}$ minimizes the truncated objective with factor $1/m$, as in (20), rather than (29) run on the $m-1$ points of $S^{\setminus i}$ with factor $1/(m-1)$. The minimizers are given as hypotheses (any minimizers, for this $S$ and $i$). The integral $d\theta$ is against the reference measure $\nu$, assumed σ-finite. Losses are nonnegative, as the paper's costs are ($c:Y\times Y\to\mathbb R_+$, p. 502). The objectives take values in $[0,\infty]$, so a density with infinite relative entropy to $f_0$ cannot be a minimizer. The display just before Theorem 24 writes $\ell(g,z)$ inside the sum; (29) has $\ell(g,z_i)$, which is used.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 518, Theorem 24 (Eq. (29)); setting §5.2.3, p. 517, Eq. (28)

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

namespace StabGen.Entropy

open MeasureTheory

/-- Theorem 24, p. 518, in the pairwise form of its proof: `Θ` carries a σ-finite reference
measure `ν`, the base loss `r(h_θ, z)` is measurable in `θ` and bounded, `0 ≤ r ≤ M`, `f0` is a
probability density and `λ > 0`. If `f` minimizes (29) over all probability densities and `f'`
(the paper's `f^{\i}`) minimizes the truncated objective (factor `1/m`, term `i` removed) over all
probability densities, then for every `z`, `|ℓ(f, z) − ℓ(f', z)| ≤ M²/(λm)`, `ℓ` being (28). -/
theorem entropy_regularization_uniform_stability {Θ Z : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [SigmaFinite ν]
    (r : Θ → Z → ℝ) (M : ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (f0 : Θ → ℝ) (hf0 : IsDensity ν f0) (lam : ℝ) (hlam : 0 < lam)
    {m : ℕ} (S : Fin m → Z) (i : Fin m) (f f' : Θ → ℝ)
    (hf : IsDensity ν f)
    (hfmin : ∀ g, IsDensity ν g → entropyRegRisk ν r f0 lam S f ≤ entropyRegRisk ν r f0 lam S g)
    (hf' : IsDensity ν f')
    (hf'min : ∀ g, IsDensity ν g →
      truncEntropyRegRisk ν r f0 lam S i f' ≤ truncEntropyRegRisk ν r f0 lam S i g) :
    ∀ z : Z, |avgLoss ν r f z - avgLoss ν r f' z| ≤ M ^ 2 / (lam * (m : ℝ)) := by sorry

end StabGen.Entropy
