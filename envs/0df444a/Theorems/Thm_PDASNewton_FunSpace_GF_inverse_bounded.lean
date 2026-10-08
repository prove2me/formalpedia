-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_GF_inverse_bounded
-- name    : PDASNewton.FunSpace.GF_inverse_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:14.642264+00:00
-- url     : https://prove2.me/theorems/8d485c97-f794-48c5-ba0a-26d86201c6af
-- title:
--   Proof of Theorem 4.1, p. 23 — G_F(z) = βI + G_m(Cz − f + βψ)C is invertible on L² with ‖G_F(z)⁻¹‖ bounded uniformly in z
-- statement:
--   Let $(\Omega, \mu)$ be a finite measure space, $q > 2$, and let $A \in \mathcal{L}(L^2(\Omega))$ be self-adjoint with (H1): $(Ay, y) \ge \gamma\|y\|^2$ for some $\gamma > 0$ and all $y \in L^2(\Omega)$. Assume (H2): $A = C + \beta I$ with $\beta > 0$ and $C \in \mathcal{L}(L^2(\Omega), L^q(\Omega))$, and let $f, \psi \in L^q(\Omega)$. For $z \in L^2(\Omega)$ let
--   $$G_F(z) = \beta I + G_m(Cz - f + \beta\psi)\,C,$$
--   where $G_m(u)(x) = 1$ if $u(x) \ge 0$ and $0$ if $u(x) < 0$ ((4.1) with $\delta = 1$). Then there is $M$ such that for all $z, g \in L^2(\Omega)$ the equation $G_F(z)h = g$ has exactly one solution $h \in L^2(\Omega)$, and this solution satisfies
--   $$\|h\|_{L^2} \le M\,\|g\|_{L^2}.$$
--
--   This is the invertibility hypothesis of Theorem 1.1 for the reduced map: in block form, with $\mathcal{I} = \{Cz - f + \beta\psi \ge 0\}$ and $\mathcal{A}$ its complement, $G_F(z)$ is upper block triangular with diagonal blocks $\beta I_{\mathcal{I}} + C_{\mathcal{I}}$ and $\beta I_{\mathcal{A}}$.
--
--   **Formalization Note** The page says that each $G_F(z)$ has a bounded inverse; Theorem 1.1 needs the bound uniform in $z$, and the block form gives it with $M$ depending only on $\beta$, $\gamma$ and $\|C\|$. The uniform form is stated. The equation $G_F(z)h = g$ is written almost everywhere on representatives. Self-adjointness and $f, \psi \in L^q$ are standing assumptions of §4 and Theorem 4.1, kept for uniformity.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 23, Appendix A, proof of Theorem 4.1, last paragraph; (H1) p. 12, (H2) p. 13

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

open MeasureTheory
open scoped ENNReal

/-- Proof of Theorem 4.1, p. 23: under (H1), (H2), the operators
`G_F(z) = β I + G_m(C z - f + β ψ) C` (`δ = 1`) are invertible on `L²` with inverses bounded
uniformly in `z`: for all `z, g ∈ L²` the equation `G_F(z) h = g` has exactly one solution
`h ∈ L²`, and it satisfies `‖h‖ ≤ M ‖g‖` with `M` independent of `z` and `g`. -/
theorem GF_inverse_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 2 < q)
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA_sa : ∀ u v : Lp ℝ 2 μ, inner ℝ (A u) v = inner ℝ u (A v))
    (γ : ℝ) (hγ : 0 < γ) (hH1 : ∀ y : Lp ℝ 2 μ, γ * ‖y‖ ^ 2 ≤ inner ℝ (A y) y)
    (β : ℝ) (hβ : 0 < β) (C : Lp ℝ 2 μ →L[ℝ] Lp ℝ q μ)
    (hAC : ∀ y : Lp ℝ 2 μ, (A y : α → ℝ) =ᵐ[μ] fun x => C y x + β * y x)
    (f ψ : Lp ℝ 2 μ) (hf : MemLp (f : α → ℝ) q μ) (hψ : MemLp (ψ : α → ℝ) q μ) :
    ∃ M : ℝ, ∀ z g : Lp ℝ 2 μ,
      (∃! h : Lp ℝ 2 μ,
        ∀ᵐ x ∂μ, β * h x + gm 1 (C z x - f x + β * ψ x) * C h x = g x) ∧
      ∀ h : Lp ℝ 2 μ,
        (∀ᵐ x ∂μ, β * h x + gm 1 (C z x - f x + β * ψ x) * C h x = g x) →
        ‖h‖ ≤ M * ‖g‖ := by sorry

end PDASNewton.FunSpace
