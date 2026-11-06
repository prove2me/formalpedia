-- Prove2me | Theorems.Thm_RankOneSK_theorem_2_11
-- name    : RankOneSK.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:30.124762+00:00
-- url     : https://prove2.me/theorems/74da2e0f-65c2-4a15-8580-033af225f629
-- title:
--   Theorem 2.11 — Sudakov–Fernique comparison with deterministic shifts $m_i$ over a countable index set
-- statement:
--   Let $I$ be a countable index set and let $\{X_i\}_{i\in I}$, $\{Y_i\}_{i\in I}$ be mean-zero Gaussian processes (all finite-dimensional distributions Gaussian) such that
--   $$\mathbb E(X_i-X_j)^2\le\mathbb E(Y_i-Y_j)^2\qquad\text{for all }i,j\in I .$$
--   Let $m_i\in\mathbb R$, $i\in I$, be deterministic.
--
--   **Theorem 2.11** (Vitale). If $\sup_i(Y_i+m_i)$ is almost surely finite and integrable, then so is $\sup_i(X_i+m_i)$, and
--   $$\mathbb E\sup_{i\in I}(X_i+m_i)\ \le\ \mathbb E\sup_{i\in I}(Y_i+m_i).$$
--
--   The paper applies it on a countable dense subset of the unit sphere, with $X_z=z^\top Jz$, $Y_z=\frac{2\beta}{\sqrt n}g^\top z$ and $m_z=-\rho\|z\|^2_{\le\delta n}$, in the proof of Lemma 2.10.
--
--   Differences from the source:
--   - generalization: {X_i} and {Y_i} on one probability space → X and Y on two possibly different probability spaces; reason: taking the same space gives the source
--   - encoding: E sup_i (X_i + m_i) ⩽ E sup_i (Y_i + m_i), extended-real expectations → if sup_i (Y_i + m_i) is a.s. finite and integrable, then sup_i (X_i + m_i) is a.s. finite, integrable, and has the smaller Bochner integral; reason: when E sup(Y + m) = +∞ the source inequality is empty, and for nonempty I the suprema are bounded below by an integrable variable; for empty I both sides are 0
--   - reading: trailing "∀ i ∈ I" after the conclusion → dropped; reason: the conclusion has no free i; it is a slip
--   - encoding: mean-zero Gaussian process, E(X_i − X_j)² → IsGaussianProcess, ∫ X_i = 0, ∫ (X_i − X_j)²; reason: Mathlib definitions; Gaussian variables have finite moments
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Theorem 2.11, p.15 (PDF p.16), citing [Vit00]

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RankOneSK

/-- **Theorem 2.11 (Variant of Sudakov–Fernique comparison inequality [Vit00]).** Let `I` be a countable
index set. Suppose `{X_i}_{i∈I}` and `{Y_i}_{i∈I}` are two mean-zero Gaussian processes such that
`E(X_i − X_j)² ⩽ E(Y_i − Y_j)²` for all `i, j ∈ I`. Let `{m_i}_{i∈I}` be deterministic reals. Then
`E sup_i (X_i + m_i) ⩽ E sup_i (Y_i + m_i)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Theorem 2.11, p.15.

**Formalization Note** The two processes may live on different probability spaces. Gaussian process
is Mathlib's `IsGaussianProcess` (all finite-dimensional laws Gaussian), so means and second moments are
finite. `E sup` is an extended-real quantity in the source; the inequality has content only when the right
side is finite, so the statement assumes that `sup_i (Y_i + m_i)` is a.s. finite and integrable and
concludes that `sup_i (X_i + m_i)` is a.s. finite, integrable, and has the smaller mean (if `I` is
nonempty, this is equivalent to the extended-real inequality). The source's trailing "∀ i ∈ I" is a slip
and is dropped. -/
theorem theorem_2_11 {I : Type*} [Countable I] {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (X : I → Ω → ℝ) (Y : I → Ω' → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P')
    (hX0 : ∀ i, ∫ ω, X i ω ∂P = 0) (hY0 : ∀ i, ∫ ω, Y i ω ∂P' = 0)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P')
    (m : I → ℝ)
    (hYbdd : ∀ᵐ ω ∂P', BddAbove (Set.range fun i => Y i ω + m i))
    (hYint : Integrable (fun ω => ⨆ i, Y i ω + m i) P') :
    (∀ᵐ ω ∂P, BddAbove (Set.range fun i => X i ω + m i)) ∧
      Integrable (fun ω => ⨆ i, X i ω + m i) P ∧
      ∫ ω, (⨆ i, X i ω + m i) ∂P ≤ ∫ ω, (⨆ i, Y i ω + m i) ∂P' := by sorry

end RankOneSK
