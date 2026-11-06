-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_3_5
-- name    : SKWeakPoincare.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:25.887661+00:00
-- url     : https://prove2.me/theorems/b4f3d66f-41dd-4f6a-9bce-7078ad853163
-- title:
--   Lemma 3.5 — Gaussian isoperimetry on Wiener space: nearby paths in two sets of measure $>v/4$
-- statement:
--   Let $T>0$, let $\gamma$ be Wiener measure on $C([0,T];\mathbb R^n)$, and let $0<v\le1/2$.
--
--   1. If $A_-,A_+$ are Borel subsets of $C_0([0,T];\mathbb R^n)$ with $\gamma(A_-),\gamma(A_+)>v/4$, there are $\omega\in A_-$ and $h\in H_T$ with $\omega+h\in A_+$ and
--   $$
--   \|h\|_{H_T}\le2\sqrt{2\log(4/v)}.
--   $$
--   2. For every Borel function $F$ with quantile function $Q_F$ under $\gamma$, there are $\omega\in C_0([0,T];\mathbb R^n)$ and $h\in H_T$ with
--   $$
--   F(\omega)\le Q_F(v),\qquad F(\omega+h)\ge Q_F(1-v),\qquad \|h\|_{H_T}\le2\sqrt{2\log(4/v)}.
--   $$
--
--   This is the consequence of Borell's Gaussian isoperimetric inequality used to find a lower-quantile path and an upper-quantile path at small Cameron–Martin distance (proof of Lemma 6.1).
--
--   **Formalization Note** $\gamma$ is any measure satisfying `IsWienerMeasure`. Sets and $F$ are taken on the whole path space, and membership in $C_0$ is the condition $\omega_0=0$.
--
--   Differences from the source:
--   - encoding: Wiener measure γ → any γ with IsWienerMeasure T n γ; reason: the law of a continuous standard Brownian path on [0,T]; all such laws coincide
--   - encoding: Borel subsets A₋, A₊ of C₀([0,T];ℝⁿ) → measurable subsets of C([0,T];ℝⁿ) contained in {ω | ω₀ = 0}; reason: C₀ is closed, so its Borel subsets are exactly these sets
--   - encoding: a Borel F on C₀([0,T];ℝⁿ), with ω ∈ C₀ implicit → a measurable F on C([0,T];ℝⁿ), and ω₀ = 0 required in the conclusion; reason: every Borel F on the closed set C₀ extends to a Borel F on C([0,T];ℝⁿ), and Q_F only depends on F on C₀ since γ(C₀) = 1
--   - encoding: h ∈ H_T with ‖h‖_{H_T} → IsCMShift g h with cmNorm T g; reason: h ∈ H_T iff h = ∫₀ˢ g with g ∈ L², ‖h‖_{H_T} = ‖g‖_{L²}
--   - encoding: Q_F(v) = inf{a : γ[F ≤ a] ≥ v} → quantile γ F v, a real sInf; reason: for 0 < v < 1 the set is nonempty and bounded below, so sInf is the infimum
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 3.5, p.16 ([Bor75, Theorem 3.1])

import Mathlib
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKWeakPoincare_IsWienerMeasure

open MeasureTheory

namespace SKWeakPoincare

/-- **Lemma 3.5 (Gaussian isoperimetry on Wiener space, [Bor75, Theorem 3.1]).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 3.5, p. 16.

Let `0 < v ≤ 1/2`, `T > 0`, and `γ` Wiener measure on `C([0, T]; ℝ^n)`.
(a) If `A₋, A₊` are Borel subsets of `C₀([0, T]; ℝ^n)` with `γ(A₋), γ(A₊) > v/4`, there are `ω ∈ A₋`
and `h ∈ H_T` with `ω + h ∈ A₊` and `‖h‖_{H_T} ≤ 2√(2 log(4/v))`.
(b) For every Borel `F`, writing `Q_F` for its quantile function under `γ`, there are `ω` and
`h ∈ H_T` with `F(ω) ≤ Q_F(v)`, `F(ω + h) ≥ Q_F(1 − v)` and `‖h‖_{H_T} ≤ 2√(2 log(4/v))`.

**Formalization Note.** Sets and `F` live on the whole path space `C([0, T]; ℝ^n)`; "`A ⊆ C₀`" is
`A ⊆ {ω | pathExt ω 0 = 0}`, and the point `ω` of (b) is required to lie in `C₀`. A Borel `F` on the
closed set `C₀` is the restriction of a Borel `F` on the whole space, and `Q_F` only depends on `F` on
`C₀`, which carries `γ`. `h ∈ H_T` is `IsCMShift g h` with `‖h‖_{H_T} = cmNorm T g`. -/
theorem lemma_3_5 (T : ℝ) (hT : 0 < T) (n : ℕ) (γ : Measure (PathSpace T n))
    (hγ : IsWienerMeasure T n γ) (v : ℝ) (hv0 : 0 < v) (hv : v ≤ 1 / 2) :
    (∀ Am Ap : Set (PathSpace T n), MeasurableSet Am → MeasurableSet Ap →
      Am ⊆ {ω | pathExt ω 0 = 0} → Ap ⊆ {ω | pathExt ω 0 = 0} →
      ENNReal.ofReal (v / 4) < γ Am → ENNReal.ofReal (v / 4) < γ Ap →
      ∃ ω ∈ Am, ∃ (h : PathSpace T n) (g : ℝ → EuclideanSpace ℝ (Fin n)),
        IsCMShift g h ∧ ω + h ∈ Ap ∧ cmNorm T g ≤ 2 * Real.sqrt (2 * Real.log (4 / v))) ∧
    (∀ F : PathSpace T n → ℝ, Measurable F →
      ∃ (ω h : PathSpace T n) (g : ℝ → EuclideanSpace ℝ (Fin n)),
        pathExt ω 0 = 0 ∧ IsCMShift g h ∧ F ω ≤ quantile γ F v ∧
        quantile γ F (1 - v) ≤ F (ω + h) ∧
        cmNorm T g ≤ 2 * Real.sqrt (2 * Real.log (4 / v))) := by sorry

end SKWeakPoincare
