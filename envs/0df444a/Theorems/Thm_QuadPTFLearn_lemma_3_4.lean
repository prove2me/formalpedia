-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_3_4
-- name    : QuadPTFLearn.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:06.53495+00:00
-- url     : https://prove2.me/theorems/9ae532ee-8620-4c03-9672-688c30b91af3
-- title:
--   Lemma 3.4, p.17 — Gaussian comparison $|\mathbb E F(p)-\mathbb E F(\tilde p)|\le O(k^2\tau D_2(F))$
-- statement:
--   **Gaussian comparison.** Let $\tau\in(0,1)$, $V\subseteq\mathbb R^d$ and $p_1,\dots,p_k$ polynomials of degree at most two with $\|p_i\|_2=1$ and coefficient norms $\|b_i\|_2,\|L_i\|_{op},\|A_i\|_{op}\le\tau$ (the assumptions of Lemma 3.3), with Gaussian replacements $\tilde p_i(x_V,z)=q_i(x_V)+\theta_i\cdot z$. Let $F:\mathbb R^k\to\mathbb R$ be $C^2$ with $D_2(F):=\max_{i,j}\|\partial_i\partial_jF\|_\infty<\infty$. Then
--   $$\Big|\mathbb E_x\big[F(p_1(x),\dots,p_k(x))\big]-\mathbb E_{x,z}\big[F(\tilde p_1(x_V,z),\dots,\tilde p_k(x_V,z))\big]\Big|\le Ck^2\tau D_2(F)$$
--   for a universal constant $C$.
--
--   Regular quadratics jointly behave like Gaussians with the same covariance, which is what lets intersections of quadratic PTFs be compared with intersections of halfspaces.
--
--   Differences from the source:
--   - encoding: O(k²τD₂(F)) with D₂(F) < ∞ → C k² τ D₂ for a universal C chosen first and every bound D₂ on the second partial derivatives; reason: the statement for every bound is the statement for the supremum
--   - encoding: the assumptions of Lemma 3.3; E_{x,z} → `Lemma33Assumptions`; the iterated integral over x ∼ N(0, I_d) and z ∼ N(0, I_N); reason: the same objects; x and z are independent
--   - encoding: i ∈ [k], k ∈ ℤ₊ → k a natural number, k = 0 not excluded; reason: at k = 0 F is a constant and both expectations agree; no instance of the source changes
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 3.4 (Gaussian comparison), p.17 (PDF p.19); assumptions of Lemma 3.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_QuadPTFLearn_Regularity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 3.4 (Gaussian comparison), p.17 (PDF p.19).

Let `τ, V, p₁, …, p_k` satisfy the assumptions of Lemma 3.3. Let `F : ℝᵏ → ℝ` be `C²` with
`D₂(F) := max_{i,j} ‖∂ᵢ∂ⱼF‖_∞ < ∞`. Then
`|E_x[F(p₁(x), …, p_k(x))] − E_{x,z}[F(p̃₁(x_V, z), …, p̃_k(x_V, z))]| ≤ O(k² τ D₂(F))`.

**Formalization Note.** `O(·)` is a universal constant `C` chosen first; `D₂` is any bound on the
second partial derivatives. `z ∼ N(0, I_N)` independent of `x`. -/
theorem lemma_3_4 :
    ∃ C : ℝ, ∀ (d k : ℕ) (τ : ℝ) (V : Submodule ℝ (Pt d)) (p : Fin k → Poly d),
      Lemma33Assumptions τ V p →
      ∀ F : (Fin k → ℝ) → ℝ, ContDiff ℝ 2 F → ∀ D₂ : ℝ, (∀ i j y, |pd2 F i j y| ≤ D₂) →
        |∫ x, F (fun i => peval (p i) x) ∂gauss d -
            ∫ x, ∫ G, F (fun i => ptilde V (p i) x G) ∂stdGaussian (Lift d) ∂gauss d| ≤
          C * (k : ℝ) ^ 2 * τ * D₂ := by sorry

end QuadPTFLearn
