-- Prove2me | Theorems.Thm_SPOBounds_Natarajan_Supplement_linear_rademacher_bound
-- name    : SPOBounds.Natarajan.Supplement.linear_rademacher_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:42:53.094199+00:00
-- url     : https://prove2.me/theorems/30276dfe-2341-4dac-844b-1b8bf4bb4660
-- title:
--   Theorem 6 — $\mathfrak R^n(\mathcal H_{\mathcal B})\le\Omega\beta\sqrt{2/(\alpha n)}$ for linear classes in a strongly convex level set
-- statement:
--   Let $\|\cdot\|$ be a norm on the space $\mathbb R^{d\times p}$ of real matrices and $\|\cdot\|_*$ its dual norm with respect to the trace pairing $\langle B,A\rangle=\sum_{i,j}B_{ij}A_{ij}$. Let $\mathcal S\subseteq\mathbb R^{d\times p}$ be a closed convex set, and let $F:\mathcal S\to\mathbb R$ be $\alpha$-strongly convex with respect to $\|\cdot\|_*$ and satisfy $\inf_{B\in\mathcal S}F(B)=0$. Suppose $\mathcal B\subseteq\{B\in\mathcal S:F(B)\le\beta^2\}$, and let $\Omega$ be such that
--   $$\sup_{\sigma\in\{\pm1\}^d}\ \sup_{x\in\mathcal X}\ \|\sigma x^\top\|\le\Omega,$$
--   where $\mathcal X\subseteq\mathbb R^p$ is the feature domain. Let $\mathcal H_{\mathcal B}=\{x\mapsto Bx:B\in\mathcal B\}$. Then, for every distribution $\mathcal D$ of (feature, cost) pairs whose feature lies in $\mathcal X$ almost surely and every sample size $n\ge1$,
--   $$\mathfrak R^n(\mathcal H_{\mathcal B})\le\Omega\beta\sqrt{\frac{2}{\alpha n}},$$
--   where $\mathfrak R^n$ is the expected multivariate Rademacher complexity over an i.i.d. sample of size $n$.
--
--   Combined with Theorems 4 and 5, this gives margin-based SPO generalization bounds for regularized linear models whose dependence on the dimensions $p$ and $d$ enters only through $\Omega$ and $\beta$.
--
--   **Formalization Note** The prediction $Bx$ is the cost functional $c\mapsto c^\top(Bx)$ on Euclidean $\mathbb R^d$, so $\mathfrak R^n$ is the published `SPOBounds.Margin.expRademacherMulti`. Features live in Euclidean $\mathbb R^p$ with its Borel σ-algebra. No integrability hypothesis is assumed. Strong convexity and $\inf F=0$ make the level set bounded; the supremum of the resulting bounded family of linear maps is Lipschitz in a finite feature sample. The $\Omega$ bound controls it almost surely, so the empirical complexity is integrable. Lean's default value for a nonintegrable Bochner integral is therefore not needed on these instances. $\Omega\ge0$ follows from the hypotheses, because $\mathcal X$ is nonempty (the feature lies in it almost surely) and norms are nonnegative.
--
--   Differences from the source:
--   - reading: "$\alpha$-strongly convex" and the level $\beta^2$ → explicit hypotheses $\alpha>0$ and $\beta\ge0$; reason: strong convexity with a positive modulus is the meaning of the term, and the printed $\beta^2$ presupposes $\beta\ge0$ (with $\beta<0$ and $\mathcal B$ the set of minimizers the printed bound is negative while $\mathfrak R^n(\mathcal H_{\mathcal B})=0$).
--   - encoding: features in $\mathcal X\subseteq\mathbb R^p$, a sample size $n$, and a norm on $\mathbb R^{d\times p}$ → a distribution on (feature, cost) pairs with features in $\mathcal X$ almost surely, $n>0$, and a definite seminorm; reason: these restate the source's set-up (the source divides by $n$) and change no instance.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 21, Theorem 6 (proof in Appendix C.2, p. 34)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Rademacher
import Definitions.Def_SPOBounds_Natarajan_Supplement_LinearClass

open MeasureTheory SPOBounds.Margin

namespace SPOBounds.Natarajan.Supplement

/-- **Theorem 6** (arXiv:1905.11488v3, p. 21). Let `N` be a norm on `ℝ^{d×p}` and `N_*` its dual
norm under the trace pairing. Let `𝒮 ⊆ ℝ^{d×p}` be closed and convex, `F` `α`-strongly convex on
`𝒮` with respect to `N_*` (`α > 0`) with `inf_{B ∈ 𝒮} F(B) = 0`, `ℬ ⊆ {B ∈ 𝒮 : F(B) ≤ β²}`
(`β ≥ 0`), and `Ω` such that `N(σ xᵀ) ≤ Ω` for all `σ ∈ {±1}^d` and `x ∈ 𝒳 ⊆ ℝ^p`. For any
distribution `D` of (feature, cost) pairs whose feature lies in `𝒳` almost surely and any `n > 0`,
the expected multivariate Rademacher complexity of the linear class `𝓗_ℬ = {x ↦ Bx : B ∈ ℬ}`
satisfies `ℜⁿ(𝓗_ℬ) ≤ Ω β √(2 / (α n))`. -/
theorem linear_rademacher_bound {d p : ℕ}
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    [BorelSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (N : Seminorm ℝ (Matrix (Fin d) (Fin p) ℝ)) (hN : IsMatrixNorm N)
    (𝒮 : Set (Matrix (Fin d) (Fin p) ℝ)) (h𝒮c : IsClosed 𝒮) (h𝒮v : Convex ℝ 𝒮)
    (F : Matrix (Fin d) (Fin p) ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (hF : StronglyConvexWrt (dualNorm N) 𝒮 α F) (hinf : IsGLB (F '' 𝒮) 0)
    (ℬ : Set (Matrix (Fin d) (Fin p) ℝ)) (β : ℝ) (hβ : 0 ≤ β)
    (hℬ : ℬ ⊆ {B | B ∈ 𝒮 ∧ F B ≤ β ^ 2})
    (𝒳 : Set (EuclideanSpace ℝ (Fin p))) (Ω : ℝ)
    (hΩ : ∀ σ : Fin d → Bool, ∀ x ∈ 𝒳, N (signOuter σ x) ≤ Ω)
    (D : Measure (EuclideanSpace ℝ (Fin p) × StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    [IsProbabilityMeasure D] (hD𝒳 : ∀ᵐ z ∂D, z.1 ∈ 𝒳)
    (n : ℕ) (hn : 0 < n) :
    expRademacherMulti D (linearClass ℬ) n ≤ Ω * β * Real.sqrt (2 / (α * n)) := by sorry

end SPOBounds.Natarajan.Supplement
