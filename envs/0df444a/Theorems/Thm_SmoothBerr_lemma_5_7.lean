-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_7
-- name    : SmoothBerr.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:12.595734+00:00
-- url     : https://prove2.me/theorems/69dc020a-4793-45c7-a2a9-5e92902eae84
-- title:
--   Lemma 5.7 — a normal to Gaussian rows: $\mathbb E\langle w,u\rangle^2\le 2\|w\|_2^2/(n-2a^2-2)$
-- statement:
--   Let $B=G+M\in\mathbb R^{(n-1)\times n}$, where $G$ has iid $\mathcal N(0,1)$ entries and $M$ is a deterministic matrix with $\|M\|_2\le a$. Let $u$ be a unit vector orthogonal to the rows of $B$. If $n>2a^2+2$, then for every deterministic $w\in\mathbb R^n$,
--   $$
--   \mathbb E\big[|\langle w,u\rangle|^2\big]\le\frac{2\|w\|_2^2}{n-2a^2-2}.
--   $$
--   The unit normal to $n-1$ shifted Gaussian rows is spread out: its projection on any fixed direction has second moment of order $1/n$, uniformly over shifts of norm $O(\sqrt n)$. This drives the small-ball estimate of Lemma 5.4.
--
--   **Formalization Note** $u$ is any measurable function of $G$ that is almost surely a unit vector with $Bu=0$; the expectation is a lower Lebesgue integral of $\langle w,u\rangle^2$.
--
--   Differences from the source:
--   - reading: let u be a unit vector orthogonal to the row vectors of B → every measurable u(G) with, a.s., uᵀu = 1 and B u = 0; reason: B has rank n − 1 a.s., so u is determined up to sign and ⟨w,u⟩² does not depend on the choice
--   - encoding: E[|⟨w,u⟩|²] → lower Lebesgue integral of ENNReal.ofReal ⟨w,u⟩² against gaussianMatrix (n−1) n; reason: same value for a nonnegative integrand; no Bochner junk value
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Lemma 5.7, Eq. (14), p.14

import Mathlib
import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Lemma 5.7 (A normal to Gaussian rows)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Lemma 5.7, Eq. (14), p.14).

Let `B = G + M ∈ ℝ^{(n−1)×n}`, where `G` is a standard Gaussian matrix and `M` is a deterministic
matrix with `‖M‖₂ ≤ a`. Let `u` be a (random) unit vector orthogonal to the rows of `B`. If
`n > 2a² + 2`, then for every deterministic `w ∈ ℝⁿ`,
`E[|⟨w, u⟩|²] ≤ 2‖w‖₂² / (n − 2a² − 2)`.

**Formalization Note** `u` is any measurable function of `G` that is almost surely a unit vector
with `B u = 0` (such `u` exist, and `⟨w,u⟩²` does not depend on the choice of sign). The
expectation is a lower Lebesgue integral (`∫⁻`) of `ENNReal.ofReal ⟨w,u⟩²`, so it cannot be made
small by a non-integrable integrand. `‖w‖₂²` is `w ⬝ᵥ w`; `‖M‖₂` is `specNorm`. `n − 1` is natural
subtraction; `n > 2a² + 2 ≥ 2` gives `n ≥ 3`. -/
theorem lemma_5_7 (n : ℕ) (a : ℝ) (hn : 2 * a ^ 2 + 2 < (n : ℝ))
    (M : Matrix (Fin (n - 1)) (Fin n) ℝ) (hM : specNorm M ≤ a)
    (u : (Fin (n - 1) → Fin n → ℝ) → (Fin n → ℝ)) (hu : Measurable u)
    (hunit : ∀ᵐ g ∂(gaussianMatrix (n - 1) n),
      u g ⬝ᵥ u g = 1 ∧ (Matrix.of g + M) *ᵥ u g = 0)
    (w : Fin n → ℝ) :
    ∫⁻ g, ENNReal.ofReal ((w ⬝ᵥ u g) ^ 2) ∂(gaussianMatrix (n - 1) n) ≤
      ENNReal.ofReal (2 * (w ⬝ᵥ w) / ((n : ℝ) - 2 * a ^ 2 - 2)) := by sorry

end SmoothBerr
