-- Prove2me | Theorems.Thm_WeakMFG_Existence_theorem_3_5
-- name    : WeakMFG.Existence.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:03.056177+00:00
-- url     : https://prove2.me/theorems/063e65dc-9dfc-4073-879c-36fa0d97cf57
-- title:
--   Theorem 3.5 — under (E) and (C) the mean field game in weak formulation has a solution
-- statement:
--   Assume the standing assumptions (S) (with a nonempty control set $A$), assumption (E) (sequential continuity of $b$, $f$, $g$ in the measure and control arguments on $\mathcal P_X$) and assumption (C) (convexity of the maximizer sets $A(t,x,\mu,z)$ of the Hamiltonian). Then there exists a solution of the MFG: there are $\mu\in\mathcal P_\psi(\mathcal C)$, a measurable $q:[0,T]\to\mathcal P(A)$ and a control $\alpha\in\mathbb A$ such that
--   $$V^{\mu,q}=J^{\mu,q}(\alpha),\qquad P^{\mu,\alpha}\circ X^{-1}=\mu,\qquad P^{\mu,\alpha}\circ\alpha_t^{-1}=q_t\ \text{ for a.e. } t\in[0,T].$$
--
--   The result gives existence of mean field game equilibria for path-dependent coefficients that are only measurable in the state, with mean field interaction through both the state law and the law of the control, without the Lipschitz or continuity in the state that analytic or strong-formulation approaches use.
--
--   **Formalization Note** The standing assumptions are hypotheses, with the encodings described in the model files: an abstract base space, the L² Itô layer for the state equation, nonsingularity for "$\sigma>0$", and a monotone $\rho$. The solution concept requires a density version for $\alpha$, optimality against every admissible control and every version, and the two law identities for every version. A nonempty $A$ is a disclosed reading of (S.1): the page uses it when it notes that $A(t,x,\mu,z)$ "is always nonempty".
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Theorem 3.5, §3.2, p. 11

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Theorem 3.5 (Carmona–Lacker, arXiv:1307.1152v2, §3.2, p. 11): suppose (E) and (C) hold. Then
there exists a solution of the MFG (Definition 3.4).
Formalization Notes: the standing assumptions (S) are hypotheses (`Standing`), with D1–D4;
`A` nonempty is a disclosed reading of (S.1) (the page uses it in "A(t, x, μ, z) is always
nonempty", p. 10). -/
theorem theorem_3_5 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {ψ : Path d T → ℝ}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    {A : Set EA} {Ω : Type*} [MeasurableSpace Ω] (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T)
    (hS : Standing B A ψ σ b f g X Xp)
    (hA : A.Nonempty) (hE : CondE B A ψ b f g Xp) (hC : CondC σ b f) :
    ∃ (μ : Ppsi ψ) (q : ℝ≥0 → PA A), IsMFGSolution B σ b f g Xp μ q := by sorry

end WeakMFG.Existence
