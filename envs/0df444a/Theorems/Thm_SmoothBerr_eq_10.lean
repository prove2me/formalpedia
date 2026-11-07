-- Prove2me | Theorems.Thm_SmoothBerr_eq_10
-- name    : SmoothBerr.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:51.078648+00:00
-- url     : https://prove2.me/theorems/ac3b1cf5-37f5-47c3-857a-747907076485
-- title:
--   §5, Eq. (10) — Sankar–Spielman–Teng: $\mathbb P_A[\|\hat A^{-1}v\|_2>u]\le\sqrt{2/\pi}/u$
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries, let $\Delta\in\mathbb R^{n\times n}$ be deterministic, and set $\hat A=A+\Delta$. For every fixed unit vector $v\in\mathbb R^n$ and every $u>0$,
--   $$
--   \mathbb P_A\big[\|\hat A^{-1}v\|_2>u\big]\le\frac{\sqrt{2/\pi}}u .
--   $$
--   This is Lemma 3.2 of Sankar, Spielman and Teng (2006) applied with Gaussian variance one; the paper uses it in the proof of Lemma 5.3 to show that $\|\hat A^{-1}\|_F^2$ is not too large with constant probability.
--
--   **Formalization Note** As printed, the shift $\Delta$ carries no norm bound.
--
--   Differences from the source:
--   - encoding: Â⁻¹ → Mathlib's total inverse (0 on singular Â); reason: Â is singular only on a null event (A has a density, independent of Δ); the event is empty there
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §5, Eq. (10), p.12 (citing Sankar–Spielman–Teng [50, Lemma 3.2])

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_ApproxVI_euclNorm

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **§5, Eq. (10): Sankar–Spielman–Teng [50, Lemma 3.2]** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, §5, Eq. (10), p.12).

Let `A ∈ ℝ^{n×n}` have iid `N(0,1)` entries and let `Δ ∈ ℝ^{n×n}` be a deterministic shift, with
`Â = A + Δ`. For every fixed unit vector `v ∈ ℝⁿ` and every `u > 0`,
`P_A[‖Â⁻¹v‖₂ > u] ≤ √(2/π)/u`.

**Formalization Note** As printed, `Δ` carries no norm bound. `‖·‖₂` on vectors is the published `ApproxVI.euclNorm`; `Â⁻¹` is
Mathlib's total inverse (`0` when `Â` is singular, a null event, on which the event is empty). The
existence of a unit vector forces `n ≥ 1`. -/
theorem eq_10 (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1)
    (u : ℝ) (hu : 0 < u) :
    (gaussianMatrix n n) {a | u < ApproxVI.euclNorm ((Matrix.of a + Δ)⁻¹ *ᵥ v)} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) / u) := by sorry

end SmoothBerr
