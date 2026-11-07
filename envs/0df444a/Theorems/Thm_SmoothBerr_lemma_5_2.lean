-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_2
-- name    : SmoothBerr.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:47.126092+00:00
-- url     : https://prove2.me/theorems/4ae4d7d4-970d-4562-8e2e-cc6024f38076
-- title:
--   Lemma 5.2 — control from the hidden Gaussian: $\|\hat A^{-1}\|_F^2\ge\sigma_{\min}(H+F)^{-2}$
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have iid $\mathcal N(0,1)$ entries and fix any $\Delta\in\mathbb R^{n\times n}$. A (deterministic, possibly adaptive) paired matvec algorithm performs $t$ steps against $\hat A:=A+\Delta$, with transcript $\mathcal T_t$, and $r:=n-2t\ge0$. Then there are random matrices $H,F\in\mathbb R^{r\times r}$ (measurable functions of $A$) such that $H$ has iid $\mathcal N(0,1)$ entries, $H$ is independent of the pair $(\mathcal T_t,F)$, and almost surely
--   $$
--   \|F\|_2\le\|\Delta\|_2\qquad\text{and}\qquad \|\hat A^{-1}\|_F^2\ge\sigma_{\min}(H+F)^{-2}.
--   $$
--   Thus after $t$ matvecs the Frobenius norm of the inverse is still controlled from below by the smallest singular value of a fresh shifted Gaussian matrix of size $n-2t$, which the algorithm has not seen.
--
--   **Formalization Note** $\|\cdot\|_2$ is the spectral norm, $\|\cdot\|_F^2$ the squared Frobenius norm, $\sigma_{\min}$ the smallest singular value (the published `specNorm`, `frobSq`, `sMin`). The algorithm's input and seed are fixed.
--
--   Differences from the source:
--   - reading: an algorithm computes t paired matvecs → a PairedMatvecAlg with fixed input x and seed ω (deterministic); reason: as in Theorem 5.1; the proof of Lemma 5.3 applies it conditionally on the seed
--   - encoding: r := n − 2t → hypothesis 2t ≤ n and r = n − 2t in ℕ; reason: r is a matrix dimension
--   - encoding: conditioned on T_t, there exist independent random matrices H, F with H Gaussian → law(H) = gaussianMatrix r r and H independent of (T_t, F) jointly; reason: equivalent: the conditional law of H given T_t is Gaussian and does not depend on T_t, and H ⊥ F given T_t
--   - encoding: σ_min(H + F)^{−2} → (sMin (H+F))⁻¹ ^ 2 in ℝ, which is 0 when sMin (H+F) = 0; reason: H + F is singular only on a null event when r ≥ 1 (H is Gaussian and independent of F); at r = 0 the paper's σ_min is undefined
--   - encoding: Â⁻¹ → Mathlib's total inverse (0 on singular Â); reason: Â is singular only on a null event (A has a density, independent of Δ)
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Lemma 5.2, p.10

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SmoothBerr_PairedMatvecAlg

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Lemma 5.2 (Control from the hidden Gaussian)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Lemma 5.2, p.10).

Let `A ∈ ℝ^{n×n}` have iid `N(0,1)` entries, fix any `Δ ∈ ℝ^{n×n}`, and run a (deterministic,
possibly adaptive) paired matvec algorithm with `t` steps against `Â := A + Δ`, with transcript
`T_t`. Let `r := n − 2t ≥ 0`. Then there are random matrices `H, F ∈ ℝ^{r×r}` (measurable functions
of `A`) such that `H` is Gaussian and independent of the pair `(T_t, F)`, and almost surely
`‖F‖₂ ≤ ‖Δ‖₂` and `‖Â⁻¹‖_F² ≥ σ_min(H + F)^{−2}`.

**Formalization Note** The algorithm is deterministic (input `x` and seed `ω` fixed). "Conditioned
on `T_t`, there exist independent random matrices `H, F` such that `H` is Gaussian" is encoded as:
`H` has law `gaussianMatrix r r` and is independent of `(T_t, F)` jointly, i.e. the conditional
law of `H` given `T_t` is Gaussian and does not depend on `T_t`, and `H ⊥ F` given `T_t`. The
hypothesis `2t ≤ n` states that `r = n − 2t` is a dimension. `σ_min(H+F)^{−2}` is
`(sMin (H+F))⁻¹ ^ 2`, which is `0` when `sMin (H+F) = 0` (a null event for `r ≥ 1`; for `r = 0`,
`sMin` is `0` by convention). `‖·‖₂` is `specNorm`, `‖·‖_F²` is `frobSq`, and `Â⁻¹` is Mathlib's
total inverse. -/
theorem lemma_5_2 {n t : ℕ} {ι Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (alg : PairedMatvecAlg n t ι Ω β) (x : ι) (ω : Ω) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (h2t : 2 * t ≤ n) :
    ∃ H F : (Fin n → Fin n → ℝ) → (Fin (n - 2 * t) → Fin (n - 2 * t) → ℝ),
      Measurable H ∧ Measurable F ∧
      (gaussianMatrix n n).map H = gaussianMatrix (n - 2 * t) (n - 2 * t) ∧
      IndepFun H (fun a => (alg.transcript (Matrix.of a + Δ) x ω, F a)) (gaussianMatrix n n) ∧
      ∀ᵐ a ∂(gaussianMatrix n n),
        specNorm (Matrix.of (F a)) ≤ specNorm Δ ∧
        (sMin (Matrix.of (H a) + Matrix.of (F a)))⁻¹ ^ 2 ≤ frobSq ((Matrix.of a + Δ)⁻¹) := by sorry

end SmoothBerr
