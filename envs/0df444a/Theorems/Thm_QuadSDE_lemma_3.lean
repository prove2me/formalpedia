-- Prove2me | Theorems.Thm_QuadSDE_lemma_3
-- name    : QuadSDE.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:43.366882+00:00
-- url     : https://prove2.me/theorems/95fbd659-3e12-4bba-a635-349ea5175d2c
-- title:
--   Lemma 3 — Gaussian invariance: $X(0)\sim\mathcal N(0,\sigma I)$ gives $X(t)\sim\mathcal N(0,(\sigma+qt)I)$
-- statement:
--   Let the drift be admissible (symmetric, norm and volume preserving), $q>0$ and $\sigma>0$. Let $W$ be an $N$-dimensional standard Wiener process and $X(0)=\xi$ an initial vector with i.i.d. $\mathcal N(0,\sigma)$ coordinates, independent of $W$, and let $X$ solve
--   $$dX(t)=f(X(t))\,dt+\sqrt q\,dW(t)$$
--   on every horizon. Then for every $t\ge0$,
--   $$X(t)\sim\mathcal N\big(0,(\sigma+qt)I\big).$$
--
--   The deterministic flow preserves every centered isotropic Gaussian, and the Wiener increments add variance $qt$; this makes the standard Gaussian the reference density of the expanding frame.
--
--   Differences from the source:
--   - generalization: q ∈ (0, 1] (standing assumption of APX-SDE) → any q > 0; reason: the lemma does not use q ≤ 1; the source's case is a special case
--   - generalization: X(t) solves the SDE Eq. (2) ("a unique global strong solution", p. 17) → any process X on any probability space carrying (W, Z) that solves Eq. (2) pathwise (continuous paths, integral equation a.s.); reason: with additive noise and a locally Lipschitz drift every pathwise solution agrees a.s. with the strong solution, so the statement specializes to the source's
--   - encoding: PDF 𝒩(0, σI) on ℝ^N → law equal to the product of N copies of gaussianReal 0 σ (variance σ); reason: same distribution
--   - encoding: indices in [N], time t ≥ 0 → Fin N (0-based), process time ℝ≥0, ODE time ℝ on [0, T]; reason: Lean convention; same instances
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.1, Lemma 3, p. 17

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_NoisySDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuadSDE

/-- **Lemma 3 (Gaussian invariance).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.1, Lemma 3, p. 17: "If
`X(0)` has PDF `𝒩(0, σI)`, with `σ > 0`, independently of `W`, then `X(t)` has PDF
`𝒩(0, (σ + qt)I)`."

Let the drift be admissible (Eqs. (5)–(7)), `q > 0` and `σ > 0`. If the initial vector `X(0) = ξ`
has i.i.d. `𝒩(0, σ)` coordinates and is independent of the Wiener process `W`, and `X` solves
Eq. (2) on every horizon, then for every `t ≥ 0` the coordinates of `X(t)` are i.i.d.
`𝒩(0, σ + qt)`.

**Formalization Note.** `𝒩(0, σI)` on `ℝ^N` is the product of `N` copies of `gaussianReal 0 σ`
(variance `σ`). The paper's standing range `q ≤ 1` is not needed and not assumed. -/
theorem lemma_3 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (q : ℝ) (hq : 0 < q)
    (σ : ℝ≥0) (hσ : 0 < σ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Fin N → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B)
    (ξ : Ω → Fin N → ℝ) (hξ : P.map ξ = Measure.pi (fun _ : Fin N => gaussianReal 0 σ))
    (hind : IndepFun ξ (fun ω t => B t ω) P) (X : ℝ≥0 → Ω → Fin N → ℝ)
    (hX : ∀ T : ℝ≥0, SolvesPathwise P (drift c) q B ξ X T) (t : ℝ≥0) :
    P.map (X t) = Measure.pi (fun _ : Fin N => gaussianReal 0 (σ + q.toNNReal * t)) := by sorry

end QuadSDE
