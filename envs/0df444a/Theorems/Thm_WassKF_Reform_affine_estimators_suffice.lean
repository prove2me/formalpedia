-- Prove2me | Theorems.Thm_WassKF_Reform_affine_estimators_suffice
-- name    : WassKF.Reform.affine_estimators_suffice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:19.198278+00:00
-- url     : https://prove2.me/theorems/cc8e6fe7-0aed-4c16-92d4-119729debcf1
-- title:
--   Proof of Theorem 2.3, (A.1b), p. 10 — under a fixed normal distribution, affine estimators attain the MMSE over all measurable ones
-- statement:
--   Let $\mathbb Q = \mathcal N_d(c, S)$ be a normal distribution of $z = [x; y]$ on $\mathbb R^d = \mathbb R^n \times \mathbb R^m$, with mean $c \in \mathbb R^d$ and positive semidefinite (possibly singular) covariance $S \in \mathbb S^d_+$. Let $\mathcal L$ be the family of all measurable functions $\mathbb R^m \to \mathbb R^n$. Then
--
--   $$
--   \inf_{\psi \in \mathcal L} \mathbb E^{\mathbb Q}\bigl[\|x - \psi(y)\|^2\bigr] = \inf_{G \in \mathbb R^{n \times m},\, g \in \mathbb R^n} \mathbb E^{\mathbb Q}\bigl[\|x - G y - g\|^2\bigr].
--   $$
--
--   In words: for a fixed Gaussian distribution, restricting the estimator to affine functions $y \mapsto G y + g$ does not increase the minimum mean square error. This is the step (A.1b) in the proof of the minimax theorem, which the paper justifies by the fact that the conditional expectation $\mathbb E^{\mathbb Q}[x \mid y]$ is affine in $y$.
--
--   **Formalization Note** Both infima are taken in $[0,\infty]$ over the lower Lebesgue integral `expectedLoss`. The affine estimator is $y \mapsto Gy + g$ written with `Matrix.mulVec` through `EuclideanSpace.equiv`. Conditional expectation does not appear in the statement.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 10, App. A.1, proof of Theorem 2.3, (A.1b)

import Mathlib
import Definitions.Def_WassKF_Reform_expectedLoss

open MeasureTheory ProbabilityTheory

namespace WassKF.Reform

/-- Proof of Theorem 2.3, step (A.1b), Shafieezadeh-Abadeh et al., arXiv:1809.08830v3, p. 10:
under a fixed normal distribution `Q = 𝒩_d(c, S)` (`S ⪰ 0`, degenerate allowed) of `z = [x; y]`,
the minimum mean square error over all measurable estimators `ψ : ℝ^m → ℝ^n` equals the minimum
over the affine estimators `y ↦ G y + g` (`G ∈ ℝ^{n×m}`, `g ∈ ℝ^n`). Both sides are infima in
`[0, ∞]` of lower Lebesgue integrals. -/
theorem affine_estimators_suffice {n m : ℕ} (c : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hS : S.PosSemidef) :
    (⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
        expectedLoss ψ (multivariateGaussian c S)) =
      ⨅ (G : Matrix (Fin n) (Fin m) ℝ) (g : EuclideanSpace ℝ (Fin n)),
        expectedLoss
          (fun y => (EuclideanSpace.equiv (Fin n) ℝ).symm
            (G.mulVec (EuclideanSpace.equiv (Fin m) ℝ y)) + g)
          (multivariateGaussian c S) := by sorry

end WassKF.Reform
