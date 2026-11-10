-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_5_2
-- name    : TruncLowDeg.Recovery.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:30.309137+00:00
-- url     : https://prove2.me/theorems/8292a3c5-cddc-4469-81e9-490d77de7608
-- title:
--   Lemma 5.2 — Gaussian integration by parts for the truncated Gaussian $\mathbb E_{\mathcal N(\mu,\Sigma)|_S}[g s_j]=\mathbb E_{\mathcal N(\mu,\Sigma)|_S}[\partial_j g]$
-- statement:
--   Let $S\subseteq\mathbb R^d$ have positive Lebesgue measure and Lebesgue-null boundary $\partial S$, let $\mu\in\mathbb R^d$ and $\Sigma\succ0$, and let $g:\mathbb R^d\to\mathbb R$ be continuously differentiable with $g(x)=0$ for all $x\in\partial S$. For a coordinate $j$ put $s_j(x)=(\Sigma^{-1}(x-\mu))_j$. If $\mathbb E_{X\sim\mathcal N(\mu,\Sigma)|_S}|g(X)s_j(X)|<\infty$ and $\mathbb E_{X\sim\mathcal N(\mu,\Sigma)|_S}|\partial_jg(X)|<\infty$, then
--   $$\mathbb E_{X\sim\mathcal N(\mu,\Sigma)|_S}[g(X)s_j(X)]=\mathbb E_{X\sim\mathcal N(\mu,\Sigma)|_S}[(\partial_jg)(X)] .$$
--   This identity is the moment equation behind system (14): with $g$ a boundary vanishing polynomial it holds for the truncated law exactly as for the untruncated Gaussian, so Algorithm 1 can recover $s_j$ from low-degree moments.
--
--   **Formalization Note.** Finiteness of $\mathbb E|\cdot|$ is `Integrable` (the functions are continuous, hence measurable); $\partial_jg(x)$ is the Fréchet derivative of $g$ at $x$ applied to the $j$-th unit vector.
--
--   Differences from the source:
--
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
--   - encoding: N(µ, Σ)|S → `truncGaussian µ Σ S = cond (multivariateGaussian µ Σ) S`; reason: the definition of §5.1; it needs no measurability of S
--   - encoding: E_{X∼N(µ,Σ)|S}|g(X)s_j(X)| < ∞ and E|∂_j g(X)| < ∞ → `Integrable` of g·s_j and of ∂_j g under `truncGaussian µ Σ S`; reason: for continuous functions, integrability is exactly finiteness of the expected absolute value
--   - encoding: ∂_j g and s_j(x) = (Σ⁻¹(x − µ))_j → `fderiv ℝ g x (EuclideanSpace.single j 1)` and `(mulV Σ⁻¹ (x − µ)) j`; reason: partial derivative of a C¹ function along e_j; matrix inverse
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 20, Lemma 5.2

import Definitions.Def_TruncLowDeg_Recovery_Basic

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 5.2 (p. 20): Gaussian integration by parts for the truncated Gaussian. If `S` has
positive Lebesgue measure and Lebesgue-null boundary, `Σ ≻ 0`, `g` is `C¹` and vanishes on `∂S`,
`s_j(x) = (Σ⁻¹(x − µ))_j`, and `g s_j` and `∂_j g` are integrable under `N(µ, Σ)|S`, then
`E_{N(µ,Σ)|S}[g s_j] = E_{N(µ,Σ)|S}[∂_j g]`. Coordinates are `0`-based; `∂_j g(x)` is the
Fréchet derivative of `g` at `x` applied to the `j`-th unit vector. -/
theorem lemma_5_2 {d : ℕ} (S : Set (Vec d)) (hSpos : 0 < volume S)
    (hbd : volume (frontier S) = 0) (μ : Vec d) (Sig : Mat d) (hSig : Sig.PosDef)
    (g : Vec d → ℝ) (hg : ContDiff ℝ 1 g) (hgb : ∀ x ∈ frontier S, g x = 0) (j : Fin d)
    (hint₁ : Integrable (fun x => g x * (mulV Sig⁻¹ (x - μ)) j) (truncGaussian μ Sig S))
    (hint₂ : Integrable (fun x => fderiv ℝ g x (EuclideanSpace.single j 1))
      (truncGaussian μ Sig S)) :
    ∫ x, g x * (mulV Sig⁻¹ (x - μ)) j ∂(truncGaussian μ Sig S) =
      ∫ x, fderiv ℝ g x (EuclideanSpace.single j 1) ∂(truncGaussian μ Sig S) := by sorry

end TruncLowDeg.Recovery
