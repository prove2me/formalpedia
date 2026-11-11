-- Prove2me | Theorems.Thm_PreservePast_lemma_5
-- name    : PreservePast.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:21.371288+00:00
-- url     : https://prove2.me/theorems/d3757e42-0ce3-40f5-b626-a003d7a6ef22
-- title:
--   Lemma 5 — spherical and Stiefel caps
-- statement:
--   1. If $V$ is uniform on the unit sphere of $\mathbb R^D$ ($D\ge1$) and $w\in\mathbb R^D$, then $\mathbb Ee^{z\langle V,w\rangle}\le\exp\big(z^2\|w\|^2/(2D)\big)$ for every $z\in\mathbb R$.
--   2. In particular, for $D\ge2$, $p_D(\theta)=\Pr\{V_1\ge\theta\}\le e^{-D\theta^2/2}$ for $\theta\ge0$.
--   3. If $V\in\mathbb R^{q\times d}$ ($1\le q\le d$) is uniform on the row-Stiefel manifold, $U=V/\sqrt q$ and $\|T\|_F\le1$, then for $\theta>0$
--   $$
--   \Pr\{\langle U,T\rangle\ge\theta\}\le\min\Big\{\frac12,\ \exp\Big[-\frac{q(d-q+1)\theta^2}2\Big]\Big\}.
--   $$
--   4. If $Z$ is uniform on the unit sphere of $\mathbb R^D$, $D\ge2$, then for every center $z_0$ and $0<\eta<1$, $\Pr\{\|Z-z_0\|\le\eta\}\le\eta^{D-1}$.
--
--   These cap and small-ball bounds are the geometric inputs of the paper's source-exponent estimates.
--
--   **Formalization Note** "Uniform" is the rotation-invariant probability law (`IsUniformSphere`, `IsHaarFrame`); the rows $V_1,\dots,V_q$ of $V$ form a Haar $q$-frame of $\mathbb R^d$ and $\langle U,T\rangle=q^{-1/2}\sum_\ell\langle V_\ell,T_\ell\rangle$. Coordinates are 0-based, so $V_1$ is coordinate `0`.
--
--   Differences from the source:
--   - encoding: V uniform on the sphere / row-Stiefel manifold → a probability law concentrated on unit vectors / orthonormal rows and invariant under all orthogonal maps; reason: this characterizes the uniform law, which exists (verification file); same instances
--   - encoding: MGF bound for V uniform on a D-dimensional sphere → the bound for D ≥ 1; reason: the sphere is empty for D = 0; excludes only undefined cases
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.2, p.18 (PDF p.20), Lemma 5, (45)–(46)

import Mathlib
import Definitions.Def_PreservePast_IsHaarFrame

open MeasureTheory

namespace PreservePast

/-- **Lemma 5 (spherical and Stiefel caps).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.2, p.18 (PDF p.20): "For a vector V
uniform on a D-dimensional unit sphere and a fixed vector w, 𝔼e^{z⟨V,w⟩} ≤ exp(z²‖w‖²/(2D))
(z ∈ ℝ). In particular p_D(θ) ≤ e^{−Dθ²/2} for θ ≥ 0. If V ∈ ℝ^{q×d} is uniform on the row-Stiefel
manifold, U = V/√q, and ‖T‖_F ≤ 1, then Pr{⟨U, T⟩ ≥ θ} ≤ min{1/2, exp[−q(d − q + 1)θ²/2]}
(θ > 0). (45) Moreover, for a uniform unit vector Z in a D-dimensional space, D ≥ 2, every center
z₀ and 0 < η < 1 satisfy Pr{‖Z − z₀‖ ≤ η} ≤ η^{D−1}. (46)" Here (p.18) "For D ≥ 2, let
p_D(θ) = Pr{V₁ ≥ θ} for V uniform on S^{D−1}."

1. The moment generating function bound, for `D ≥ 1`.
2. `p_D(θ) ≤ e^{−Dθ²/2}` for `D ≥ 2`, `θ ≥ 0`, with `V₁` the first coordinate.
3. (45), for `1 ≤ q ≤ d`: the rows `V_0, …, V_{q−1}` of `V` form a Haar `q`-frame of `ℝ^d`, and
   `⟨U, T⟩ = q^{−1/2} Σ_ℓ ⟨V_ℓ, T_ℓ⟩` for `T` with rows `T_ℓ`, `Σ_ℓ ‖T_ℓ‖² ≤ 1`.
4. (46).

**Formalization Note.** Uniform laws are the rotation-invariant probability laws `IsUniformSphere`
and `IsHaarFrame`; vectors are `EuclideanSpace ℝ (Fin D)`, coordinates 0-based. -/
theorem lemma_5 :
    (∀ (D : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin D))), 1 ≤ D → IsUniformSphere D μ →
      ∀ (w : EuclideanSpace ℝ (Fin D)) (z : ℝ),
        ∫ v, Real.exp (z * inner ℝ v w) ∂μ ≤ Real.exp (z ^ 2 * ‖w‖ ^ 2 / (2 * D))) ∧
    (∀ (D : ℕ) (hD : 2 ≤ D) (μ : Measure (EuclideanSpace ℝ (Fin D))), IsUniformSphere D μ →
      ∀ θ : ℝ, 0 ≤ θ →
        μ {v | θ ≤ v ⟨0, by omega⟩} ≤ ENNReal.ofReal (Real.exp (-(D * θ ^ 2 / 2)))) ∧
    (∀ (q d : ℕ) (μ : Measure (Fin q → EuclideanSpace ℝ (Fin d))), 1 ≤ q → q ≤ d →
      IsHaarFrame d q μ → ∀ T : Fin q → EuclideanSpace ℝ (Fin d), ∑ l, ‖T l‖ ^ 2 ≤ 1 →
      ∀ θ : ℝ, 0 < θ →
        μ {V | θ ≤ (Real.sqrt q)⁻¹ * ∑ l, inner ℝ (V l) (T l)} ≤
          ENNReal.ofReal (min (1 / 2) (Real.exp (-(q * ((d : ℝ) - q + 1) * θ ^ 2 / 2))))) ∧
    (∀ (D : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin D))), 2 ≤ D → IsUniformSphere D μ →
      ∀ (z₀ : EuclideanSpace ℝ (Fin D)) (η : ℝ), 0 < η → η < 1 →
        μ {v | ‖v - z₀‖ ≤ η} ≤ ENNReal.ofReal (η ^ (D - 1))) := by sorry

end PreservePast
