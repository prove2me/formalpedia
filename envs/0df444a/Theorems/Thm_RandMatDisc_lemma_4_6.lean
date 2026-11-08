-- Prove2me | Theorems.Thm_RandMatDisc_lemma_4_6
-- name    : RandMatDisc.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:44:19.022656+00:00
-- url     : https://prove2.me/theorems/fd4001a7-f46c-459f-9967-c4374c694fd3
-- title:
--   Lemma 4.6 — direction of a rotationally invariant vector
-- statement:
--   Let $X$ be a rotationally invariant random vector in $\mathbb R^D$ with $X\ne0$ almost surely. Then
--
--   $$U=\frac X{\|X\|}$$
--
--   is uniform on $\mathbb S^{D-1}=\{v\in\mathbb R^D:\|v\|_2=1\}$ and independent of $R=\|X\|$.
--
--   This is the standard fact that converts the rotational symmetry of the algorithm's output residual into a polar decomposition with a uniform direction.
--
--   Differences from the source:
--   - encoding: a random vector → a measurable map on a probability space; reason: definition of a random vector
--   - encoding: uniform on $\mathbb S^{D-1}$ → the law of $U$ on $\mathbb R^D$ equals the normalized surface measure `unifSphere`; reason: same law
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), Lemma 4.6, p.31 (PDF p.33)

import Definitions.Def_RandMatDisc_unifSphere

open MeasureTheory ProbabilityTheory

namespace RandMatDisc

/-- **Lemma 4.6**, Kızıldağ, Li, arXiv:2610.01591 (held file sha256 889af7fc…), p.31
(PDF p.33).

Let `X ∈ ℝᴰ` be a rotationally invariant random vector with `X ≠ 0` almost surely. Then
`U = X/‖X‖` is uniform on `S^{D−1} = {v ∈ ℝᴰ : ‖v‖₂ = 1}` and independent of `R = ‖X‖`.

**Formalization Note.** A random vector is a measurable map on a probability space.
"Uniform on `S^{D−1}`" is the normalized surface measure `unifSphere`, as a law on `ℝᴰ`.
For `D = 0` the hypothesis `X ≠ 0` a.s. cannot hold. -/
theorem lemma_4_6 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {D : ℕ} (X : Ω → EuclideanSpace ℝ (Fin D)) (hX : Measurable X)
    (hrot : IsRotInvariant P X) (hne : ∀ᵐ ω ∂P, X ω ≠ 0) :
    Measure.map (fun ω => ‖X ω‖⁻¹ • X ω) P = unifSphere (Fin D) ∧
      IndepFun (fun ω => ‖X ω‖⁻¹ • X ω) (fun ω => ‖X ω‖) P := by sorry

end RandMatDisc
