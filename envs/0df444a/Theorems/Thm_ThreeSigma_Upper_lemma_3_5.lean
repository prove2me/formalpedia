-- Prove2me | Theorems.Thm_ThreeSigma_Upper_lemma_3_5
-- name    : ThreeSigma.Upper.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:52.961359+00:00
-- url     : https://prove2.me/theorems/5de174ef-0433-45f7-b82a-11cc36149a1d
-- title:
--   Lemma 3.5 — second-derivative formula
-- statement:
--   Let $a_1,\ldots,a_m\in\mathbb R^n$ be arbitrary rows, let $\Delta>0$, and use the smooth formula
--   $$\Phi(z)=\frac1{s(z)}\sum_i\phi\left(\frac{\Delta-\langle a_i,z\rangle}{\sqrt{s(z)}}\right),\qquad s(z)=n-4-\|z\|_2^2.$$
--   Fix $z$ such that $s(z)>0$ and $\langle a_i,z\rangle<\Delta$ for every $i$. Set $t_i=(\Delta-\langle a_i,z\rangle)/\sqrt{s(z)}$. For every $v$ with $\langle z,v\rangle=0$,
--   $$s(z)^2\left.\frac{d^2}{d\lambda^2}\Phi(z+\lambda v)\right|_{\lambda=0}
--   =\sum_i\phi''(t_i)\langle a_i,v\rangle^2-\sum_i\psi(t_i)\|v\|_2^2.$$
--   This identity is the geometric derivative ingredient of the potential argument. Both derivatives are genuine iterated derivatives of the defining formulas; no norm normalization of $v$ is assumed.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with coordinates indexed 1 through n → EuclideanSpace ℝ (Fin n) with coordinates indexed 0 through n−1; reason: canonical isometric coordinate representation; no instances are excluded
--   - encoding: φ is extended-valued with φ(0)=+∞ → the real formula phi(t)=5/sinh(t²/3), whose value at zero is 0; reason: all scalar assertions and derivative evaluations use strictly positive arguments or the right limit; the extensions agree on a neighborhood of each such point
--   - encoding: Φ is specified by its smooth formula on 𝒰 → a total real formula, differentiated at z∈𝒰; reason: 𝒰 is open and all denominators and scalar gaps are positive there, so the formula agrees on a neighborhood of the evaluation point
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 3.5, p. 7, equation (6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Potential

namespace ThreeSigma.Upper

/-- Lemma 3.5, equation (6), for arbitrary rows and every orthogonal direction. -/
theorem lemma_3_5 {m n : ℕ} (a : Fin m → E n) (Δ : ℝ) (hΔ : 0 < Δ)
    (z : E n) (hz : z ∈ U a Δ) (v : E n) (hv : inner ℝ z v = 0) :
    (s z) ^ 2 * deriv (deriv (fun l : ℝ => Phi a Δ (z + l • v))) 0 =
      (∑ i, deriv (deriv phi) ((Δ - inner ℝ (a i) z) / Real.sqrt (s z)) *
        (inner ℝ (a i) v) ^ 2) -
      (∑ i, psi ((Δ - inner ℝ (a i) z) / Real.sqrt (s z)) * ‖v‖ ^ 2) := by sorry

end ThreeSigma.Upper
