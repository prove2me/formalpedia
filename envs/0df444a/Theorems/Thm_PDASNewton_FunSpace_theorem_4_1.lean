-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_theorem_4_1
-- name    : PDASNewton.FunSpace.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:29.965687+00:00
-- url     : https://prove2.me/theorems/7ada12e4-aea1-49af-862e-a17997e084da
-- title:
--   Theorem 4.1, p. 15 — under (H1), (H2), f, ψ ∈ L^q, the L² primal-dual active set strategy with c = β, λ⁰ = f − Ay⁰ converges superlinearly near y*
-- statement:
--   Let $(\Omega, \mu)$ be a finite measure space and $q > 2$ (possibly $q = \infty$). Let $A \in \mathcal{L}(L^2(\Omega))$ be self-adjoint and satisfy
--   1. (H1): $(Ay, y) \ge \gamma\|y\|^2$ for some $\gamma > 0$ and all $y \in L^2(\Omega)$;
--   2. (H2): $A = C + \beta I$ with $\beta > 0$ and $C \in \mathcal{L}(L^2(\Omega), L^q(\Omega))$.
--
--   Let $f, \psi \in L^2(\Omega)$ also belong to $L^q(\Omega)$, and let $(y^*, \lambda^*)$ solve (4.2) with $c = \beta$:
--   $$Ay^* + \lambda^* = f, \qquad \lambda^* - \max(0, \lambda^* + \beta(y^* - \psi)) = 0 \ \text{ a.e.}$$
--   Then there is $\rho > 0$ such that every run $(y^k, \lambda^k)_{k \ge 0}$ of the primal-dual active set algorithm in $L^2(\Omega)$ with $c = \beta$, started from
--   $$\|y^0 - y^*\|_{L^2} < \rho, \qquad \lambda^0 = f - Ay^0,$$
--   converges superlinearly to $(y^*, \lambda^*)$ in $L^2(\Omega) \times L^2(\Omega)$.
--
--   This is the paper's function-space result: under the norm gap $q > 2$ of (H2), which covers distributed and boundary control problems with pointwise control constraints, the active set method is a locally superlinearly convergent semismooth Newton method in $L^2$.
--
--   **Formalization Note** The page states the theorem with $\lambda^0 = \beta(y^0 - \psi)$. Its proof (pp. 22–23) needs $\lambda^0 + \beta(y^0 - \psi) = f - Cy^0 - \beta\psi$, which holds exactly for $\lambda^0 = f - Ay^0$, and uses $c = \beta$; this is the statement proved and the one formalized. The paper's bounded Lipschitz domain is replaced by an arbitrary finite measure space; the proof uses only $|\Omega| < \infty$. (H2) is $Ay = Cy + \beta y$ almost everywhere for every $y$. The solution of (4.2) is a hypothesis; it exists and is unique under (H1) (p. 12). Superlinear convergence is for the pair in the product norm $\max(\|y\|, \|\lambda\|)$: convergence, and for every $\eta > 0$ eventually $\|x^{k+1} - x^*\| \le \eta\|x^k - x^*\|$. Self-adjointness is a standing assumption of §4 and is kept.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 15, Theorem 4.1; proof in Appendix A, pp. 22–23; (H1) and (4.2) p. 12, (H2) p. 13

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 4.1, p. 15, with the initialisation the proof uses (pp. 22–23): `c = β` and
`λ⁰ = f - A y⁰` (the page prints `λ⁰ = β(y⁰ - ψ)`, which the proof does not support). -/
theorem theorem_4_1 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 2 < q)
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA_sa : ∀ u v : Lp ℝ 2 μ, inner ℝ (A u) v = inner ℝ u (A v))
    (γ : ℝ) (hγ : 0 < γ) (hH1 : ∀ y : Lp ℝ 2 μ, γ * ‖y‖ ^ 2 ≤ inner ℝ (A y) y)
    (β : ℝ) (hβ : 0 < β) (C : Lp ℝ 2 μ →L[ℝ] Lp ℝ q μ)
    (hAC : ∀ y : Lp ℝ 2 μ, (A y : α → ℝ) =ᵐ[μ] fun x => C y x + β * y x)
    (f ψ : Lp ℝ 2 μ) (hf : MemLp (f : α → ℝ) q μ) (hψ : MemLp (ψ : α → ℝ) q μ)
    (ystar lamstar : Lp ℝ 2 μ) (hsol : IsSolution A f ψ β ystar lamstar) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y lam : ℕ → Lp ℝ 2 μ, IsRun A f ψ β y lam →
      lam 0 = f - A (y 0) → ‖y 0 - ystar‖ < ρ →
      PDASNewton.Local.ConvergesSuperlinearly (fun k => (y k, lam k)) (ystar, lamstar) := by sorry

end PDASNewton.FunSpace
