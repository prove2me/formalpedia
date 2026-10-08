-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_reduced_map_slant_differentiable
-- name    : PDASNewton.FunSpace.reduced_map_slant_differentiable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:14.900485+00:00
-- url     : https://prove2.me/theorems/6489dd9e-80ce-4f8b-a997-47657f77f068
-- title:
--   Proof of Theorem 4.1, p. 23 — F(y) = βy − βψ + max(0, Cy − f + βψ) is slantly differentiable on L² with G_F(y+h) = βI + G_m(Cy − f + βψ + Ch)C, δ = 1
-- statement:
--   Let $(\Omega, \mu)$ be a finite measure space, $q > 2$, $\beta > 0$, $C \in \mathcal{L}(L^2(\Omega), L^q(\Omega))$, $A = C + \beta I$ as in (H2), and $f, \psi \in L^q(\Omega)$. Consider the reduced map $F : L^2(\Omega) \to L^2(\Omega)$,
--   $$F(y) = \beta y - \beta\psi + \max(0, Cy - f + \beta\psi),$$
--   and $G_F(y + h) = \beta I + G_m(Cy - f + \beta\psi + Ch)\,C$, where $G_m$ is (4.1) with $\delta = 1$, i.e. $G_m(u)(x) = 1$ if $u(x) \ge 0$ and $0$ if $u(x) < 0$. Then $G_F$ is a slanting function for $F$ on $L^2(\Omega)$: for every $y \in L^2(\Omega)$, writing $w = Cy - f + \beta\psi$, for every $\varepsilon > 0$ there is $\eta > 0$ such that for all $h \in L^2(\Omega)$ with $\|h\|_{L^2} < \eta$,
--   $$\big\|\max(0, w + Ch) - \max(0, w) - G_m(w + Ch)(Ch)\big\|_{L^2} \le \varepsilon\,\|h\|_{L^2}.$$
--
--   The left-hand side is exactly $\|F(y+h) - F(y) - G_F(y+h)h\|_{L^2}$, since the terms $\beta y$ and $\beta h$ cancel. This is the slant differentiability hypothesis of Theorem 1.1 for the reduced map.
--
--   **Formalization Note** The statement is written for the nonlinear term only, with the $L^2$ norm as Mathlib's `eLpNorm … 2`; the cancelled linear terms are not restated. $\delta = 1$ matches the "$\le$" in the definition of $\mathcal{I}_k$, as the page says.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 23, Appendix A, proof of Theorem 4.1, second paragraph

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

open MeasureTheory
open scoped ENNReal

/-- Proof of Theorem 4.1, p. 23: under (H2) with `q > 2` and `f, ψ ∈ L^q`, the reduced map
`F(y) = β y - β ψ + max(0, C y - f + β ψ)` is slantly differentiable on `L²` with slanting
function `G_F(y + h) = β I + G_m(C y - f + β ψ + C h) C`, `δ = 1` in (4.1). Since the `β`-terms
cancel, (A) reduces to the nonlinear term, stated here with `w = C y - f + β ψ`:
`‖max(0, w + C h) - max(0, w) - G_m(w + C h)(C h)‖_{L²} = o(‖h‖_{L²})`. -/
theorem reduced_map_slant_differentiable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 2 < q)
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (β : ℝ) (hβ : 0 < β) (C : Lp ℝ 2 μ →L[ℝ] Lp ℝ q μ)
    (hAC : ∀ y : Lp ℝ 2 μ, (A y : α → ℝ) =ᵐ[μ] fun x => C y x + β * y x)
    (f ψ : Lp ℝ 2 μ) (hf : MemLp (f : α → ℝ) q μ) (hψ : MemLp (ψ : α → ℝ) q μ)
    (y : Lp ℝ 2 μ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ h : Lp ℝ 2 μ, ‖h‖ < η →
      eLpNorm (fun x =>
          max 0 ((C y x - f x + β * ψ x) + C h x) - max 0 (C y x - f x + β * ψ x) -
            gm 1 ((C y x - f x + β * ψ x) + C h x) * C h x) 2 μ ≤
        ENNReal.ofReal (ε * ‖h‖) := by sorry

end PDASNewton.FunSpace
