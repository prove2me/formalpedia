-- Prove2me | Theorems.Thm_StabGen_Entropy_L1_displacement_bound
-- name    : StabGen.Entropy.L1_displacement_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:12:18.533402+00:00
-- url     : https://prove2.me/theorems/f191c884-b17d-48a2-8858-5499156889fd
-- title:
--   $L^1$ displacement of the posterior: $\int|f-f^{\setminus i}|\le M/(\lambda m)$
-- statement:
--   Let $\nu$ be a σ-finite reference measure on $\Theta$, let the base loss satisfy $0\le r(h_\theta,z)\le M$ with $\theta\mapsto r(h_\theta,z)$ measurable, let $f_0$ be a probability density, $\lambda>0$, and let $S=(z_1,\dots,z_m)$ be a training set and $i\in\{1,\dots,m\}$. Let $f$ be a probability density minimizing
--   $$R_r(g)=\frac1m\sum_{j=1}^m\ell(g,z_j)+\lambda K(g,f_0)$$
--   over all probability densities $g$, where $\ell$ is the averaged loss (28), and let $f^{\setminus i}$ be a probability density minimizing $R_r^{\setminus i}(g)=\frac1m\sum_{j\ne i}\ell(g,z_j)+\lambda K(g,f_0)$ over all probability densities. Then
--   $$\left(\int_\Theta|f(\theta)-f^{\setminus i}(\theta)|\,d\theta\right)^2\le\frac{M}{\lambda m}\int_\Theta|f(\theta)-f^{\setminus i}(\theta)|\,d\theta,$$
--   hence
--   $$\int_\Theta|f(\theta)-f^{\setminus i}(\theta)|\,d\theta\le\frac{M}{\lambda m}.$$
--
--   This is the central step of the proof of Theorem 24: removing one example moves the regularized posterior by at most $M/(\lambda m)$ in $L^1$.
--
--   **Formalization Note** Both displays are stated, as one conjunction. As in the proof, $f^{\setminus i}$ minimizes the truncated objective with factor $1/m$ (the analogue of (20)), not (29) run on the $m-1$ remaining points. Objectives take values in $[0,\infty]$ (see the definition file).
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 518, proof of Theorem 24 (the two displays following "by Lemma 21 we get")

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

namespace StabGen.Entropy

open MeasureTheory

/-- Proof of Theorem 24, p. 518: in the setting of Theorem 24, a minimizer `f` of (29) and a
minimizer `f'` (the paper's `f^{\i}`) of its truncated version (factor `1/m`, term `i` removed)
satisfy `(∫ |f − f'| dθ)² ≤ (M/(λm)) ∫ |f − f'| dθ`, hence `∫ |f − f'| dθ ≤ M/(λm)`. -/
theorem L1_displacement_bound {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SigmaFinite ν]
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
    (∫ θ, |f θ - f' θ| ∂ν) ^ 2 ≤ (M / (lam * (m : ℝ))) * ∫ θ, |f θ - f' θ| ∂ν ∧
      ∫ θ, |f θ - f' θ| ∂ν ≤ M / (lam * (m : ℝ)) := by sorry

end StabGen.Entropy
