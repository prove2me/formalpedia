-- Prove2me | Theorems.Thm_TaoBR_linearizedMeasure_fourier_decay_of_oscillatoryOp_le
-- name    : TaoBR.linearizedMeasure_fourier_decay_of_oscillatoryOp_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T12:39:31.446335+00:00
-- url     : https://prove2.me/theorems/1cfd7f02-55e5-4b70-a5f0-2548b342d45e
-- title:
--   Theorem 4.9, decay step — under the hypotheses of Theorem 4.9 the linearized restriction measures have power Fourier decay
-- statement:
--   Let $m - 1 \le n \le m$, let $\phi : \mathbb{R}^n \times \mathbb{R}^m \to \mathbb{R}$ and $\psi : \mathbb{R}^n \times \mathbb{R}^m \to \mathbb{C}$ be smooth, $\psi$ compactly supported, and suppose the mixed Hessian $\partial^2\phi/\partial x\,\partial y$ has rank $m - 1$ at every point of the support of $\psi$. Let $1 < p \le \infty$ and suppose that for every $\varepsilon > 0$ there is $C$ with
--   $$\|S_R\|_{L^p(\mathbb{R}^m) \to L^p(\mathbb{R}^n)} \le C R^{-m/p' + \varepsilon} \quad (R \ge 1),$$
--   where $S_R f(x) = \int e^{-2\pi i R \phi(x, y)} \psi(x, y) f(y)\,dy$ and $p'$ is the conjugate exponent. Then for every $y_0 \in \mathbb{R}^m$ and every real $q$ with $1 \le q < p$ there are $C$ and $c > 0$ such that for all $\xi \in \mathbb{R}^m$
--   $$\Bigl|\int_{\mathbb{R}^n} e^{-2\pi i \langle \xi, \nabla_y \phi(x, y_0)\rangle}\, |\psi(x, y_0)|^q \, dx\Bigr| \le C (1 + |\xi|)^{-c}.$$
--   The integral is the Fourier transform of the measure $\mu_q$, the push-forward of $|\psi(x, y_0)|^q\,dx$ under $x \mapsto \nabla_y \phi(x, y_0)$. The conclusion of Theorem 4.9 for this $q$ is the estimate $\|\hat f\|_{L^q(\mu_q)} \lesssim \|f\|_{L^q}$.
--
--   This is the step of the proof of Theorem 4.9 that T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96 (1999) 363–375 (preprint p. 10), passes over in one sentence: "Note that the hypothesis of Theorem 4.2 implies that the restriction surface $\{\nabla_y \phi(x, y_0) : x \in \mathbf{R}^n\}$ cannot degenerate to infinite order because of the Knapp counterexample. Hence one can use stationary phase to obtain some decay to Fourier transforms of measures on this surface, so that the argument in Lemma 3.1 carries over." It is not a claim the paper states, and the paper gives no further argument. Two points make it more than routine: decay of the Fourier transform needs a quantitative finite-type condition on the surface, and the weight $|\psi(\cdot, y_0)|^q$ may vanish to infinite order exactly where the surface is infinitely flat. Theorem 4.9 allows $p = 1$, where its conclusion is vacuous; this statement assumes $p > 1$, since at $p' = \infty$ the operator-norm hypothesis gives no decay to work with.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 10, the decay step in the proof of Theorem 4.9 (Fourier decay of the linearized restriction measures), which the paper asserts in one sentence and does not prove

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped ENNReal NNReal

namespace TaoBR

theorem linearizedMeasure_fourier_decay_of_oscillatoryOp_le (n m : ℕ) (hnm : m - 1 ≤ n)
    (hmn : n ≤ m) (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ (m - 1)) (p : ℝ≥0∞) (hp : 1 < p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε))) :
    ∀ y₀ : E m, ∀ q : ℝ, 1 ≤ q → ENNReal.ofReal q < p → ∃ C c : ℝ, 0 < c ∧ ∀ ξ : E m,
      ‖∫ x, Complex.exp (-(2 * Real.pi * Complex.I *
          (inner ℝ ξ (gradient (fun y => φ x y) y₀) : ℝ))) * ((‖ψ x y₀‖ ^ q : ℝ) : ℂ)‖ ≤
        C * (1 + ‖ξ‖) ^ (-c) := by
  sorry

end TaoBR
