-- Prove2me | Theorems.Thm_TeschlQM_Free_riemann_lebesgue
-- name    : TeschlQM.Free.riemann_lebesgue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T00:39:10.687336+00:00
-- url     : https://prove2.me/theorems/8792bc2e-31db-4e47-a022-f4acbdb7c8a5
-- title:
--   Lemma 7.6 (Riemann–Lebesgue) — F : L¹(ℝⁿ) → C_∞(ℝⁿ) is bounded and injective, ‖f̂‖_∞ ≤ (2π)^{−n/2}‖f‖₁
-- statement:
--   Let $C_\infty(\mathbb R^n)$ be the Banach space of continuous functions $f : \mathbb R^n \to \mathbb C$ vanishing at $\infty$, with the sup norm. For $f \in L^1(\mathbb R^n)$ the Fourier transform $\hat f(p) = (2\pi)^{-n/2}\int e^{-ipx} f(x)\,d^nx$ lies in $C_\infty(\mathbb R^n)$ and satisfies
--   $$\|\hat f\|_\infty \le (2\pi)^{-n/2}\|f\|_1 ,$$
--   and the map $f \mapsto \hat f$ from $L^1(\mathbb R^n)$ to $C_\infty(\mathbb R^n)$ is injective.
--
--   This is the basic mapping property of the Fourier transform on $L^1$.
--
--   **Formalization Note.** "Vanishes at $\infty$" is convergence to $0$ along the `cocompact` filter; the sup-norm bound is stated pointwise for every $p$; injectivity says that two integrable functions with the same transform agree almost everywhere.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 165, Lemma 7.6

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

namespace TeschlQM.Free

open MeasureTheory Filter Topology

/-- Teschl, Lemma 7.6 (Riemann–Lebesgue), p. 165: for `f ∈ L¹(ℝⁿ)` the Fourier transform `f̂`
(Teschl's normalization (7.3)) lies in `C_∞(ℝⁿ)` (continuous and vanishing at infinity), satisfies
`‖f̂‖_∞ ≤ (2π)^{-n/2} ‖f‖₁` (7.16), and the map `f ↦ f̂` is injective on `L¹(ℝⁿ)`
(functions equal almost everywhere are identified). -/
theorem riemann_lebesgue (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Integrable f volume) :
    Continuous (fourier n f) ∧
      Tendsto (fourier n f) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) ∧
      (∀ p, ‖fourier n f p‖ ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ * ∫ x, ‖f x‖) ∧
      (∀ g : EuclideanSpace ℝ (Fin n) → ℂ, Integrable g volume →
        fourier n f = fourier n g → f =ᵐ[volume] g) := by sorry

end TeschlQM.Free
