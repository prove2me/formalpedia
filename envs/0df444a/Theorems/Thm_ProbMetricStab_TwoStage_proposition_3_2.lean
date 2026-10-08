-- Prove2me | Theorems.Thm_ProbMetricStab_TwoStage_proposition_3_2
-- name    : ProbMetricStab.TwoStage.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:37.175465+00:00
-- url     : https://prove2.me/theorems/24d93634-7f44-4225-acc9-5b593aaefe38
-- title:
--   Proposition 3.2, p. 11 — f₀ is a normal convex integrand with quadratic-growth Lipschitz estimates
-- statement:
--   Consider the linear two-stage program (7)–(8) with polyhedra $X\ne\emptyset$ and $\Xi$, affine data $q(\xi),h(\xi),T(\xi)$, and the integrand $f_0$. Assume (A1): $h(\xi)-T(\xi)x\in\operatorname{pos}W$ and $q(\xi)\in D$ for all $(\xi,x)\in\Xi\times X$.
--
--   Then $f_0$ is a normal convex integrand, $f_0$ is finite on $\Xi\times X$, and there exist constants $L>0$, $\hat L>0$, $K>0$ such that for every $r\ge1$, all $\xi,\tilde\xi\in\Xi$ and all $x,\tilde x\in X$ with $\|x\|\le r$:
--
--   $$\begin{aligned}|f_0(\xi,x)-f_0(\tilde\xi,x)|&\le Lr\max\{1,\|\xi\|,\|\tilde\xi\|\}\|\xi-\tilde\xi\|,\\ |f_0(\xi,x)-f_0(\xi,\tilde x)|&\le\hat L\max\{1,\|\xi\|^2\}\|x-\tilde x\|,\\ |f_0(\xi,x)|&\le Kr\max\{1,\|\xi\|^2\}.\end{aligned}$$
--
--   The first estimate says that $f_0(\cdot,x)/(Lr)$ belongs to the Fortet–Mourier class $\mathcal F_2(\Xi)$, which is why $\zeta_2$ is the canonical metric for linear two-stage programs; the third gives the integrability needed to work on $\mathcal P_2(\Xi)$.
--
--   **Formalization Note** The page does not quantify the radius $r$ (in Lean `ρ`, since `r` is the row dimension of $W$). Read literally with $r\to0$ and $x=0$, the first and third estimates would force $f_0(\xi,0)=0$, which is false in general; the constants of the proof are uniform for $r\ge1$, so the statement has the constants first and then every $r\ge1$. The estimates compare the real values of $f_0$, which is legitimate by the finiteness conjunct (the paper notes that (A1) gives $\Xi\times X\subseteq\operatorname{dom}f_0$). Convexity of $f_0(\xi,\cdot)$ is convexity of its epigraph.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 11, Proposition 3.2

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Model

namespace ProbMetricStab.TwoStage

/-- Proposition 3.2 (p. 11): under (A1), `f₀` is a normal convex integrand, it is finite on
`Ξ × X`, and there are constants `L, L̂, K > 0` such that for every radius `ρ ≥ 1`, all
`ξ, ξ̃ ∈ Ξ` and all `x, x̃ ∈ X` with `‖x‖ ≤ ρ`:
`|f₀(ξ, x) − f₀(ξ̃, x)| ≤ L ρ max{1, ‖ξ‖, ‖ξ̃‖} ‖ξ − ξ̃‖`,
`|f₀(ξ, x) − f₀(ξ, x̃)| ≤ L̂ max{1, ‖ξ‖²} ‖x − x̃‖`, `|f₀(ξ, x)| ≤ K ρ max{1, ‖ξ‖²}`.
The page leaves the radius (written `r` there) unquantified; it is read as any `ρ ≥ 1`. -/
theorem proposition_3_2 {m s r mbar : ℕ} (P : Data m s r mbar) (hP : P.Standing) (hA1 : P.A1) :
    IsNormalConvexIntegrand P.Ξ P.f0 ∧
    (∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.f0 ξ x ≠ ⊤ ∧ P.f0 ξ x ≠ ⊥) ∧
    ∃ L Lhat K : ℝ, 0 < L ∧ 0 < Lhat ∧ 0 < K ∧
      ∀ ρ : ℝ, 1 ≤ ρ → ∀ ξ ∈ P.Ξ, ∀ ξ' ∈ P.Ξ, ∀ x ∈ P.X, ∀ x' ∈ P.X, ‖x‖ ≤ ρ →
        |(P.f0 ξ x).toReal - (P.f0 ξ' x).toReal| ≤ L * ρ * max 1 (max ‖ξ‖ ‖ξ'‖) * ‖ξ - ξ'‖ ∧
        |(P.f0 ξ x).toReal - (P.f0 ξ x').toReal| ≤ Lhat * max 1 (‖ξ‖ ^ 2) * ‖x - x'‖ ∧
        |(P.f0 ξ x).toReal| ≤ K * ρ * max 1 (‖ξ‖ ^ 2) := by sorry

end ProbMetricStab.TwoStage
