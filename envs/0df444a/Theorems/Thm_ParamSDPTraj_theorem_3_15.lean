-- Prove2me | Theorems.Thm_ParamSDPTraj_theorem_3_15
-- name    : ParamSDPTraj.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:08.104972+00:00
-- url     : https://prove2.me/theorems/8ed3f44e-9ae5-4688-946b-147d99e0a4e5
-- title:
--   Theorem 3.15 (corrected: irregular accumulation via right-sided continuous loss of uniqueness) — every optimal point unique from the left is one of six types
-- statement:
--   Consider the primal-dual pair of parametric semidefinite programs $(P_t)$, $(D_t)$ on the open interval $T=(t_i,t_f)$, under Assumptions 3.1 (LICQ and uniform boundedness of $\mathcal A$), 3.2 (strict feasibility) and 3.3 (data continuity). Let $t^*\in T$.
--
--   1. Let $X^*\in\mathcal P^*(t^*)$. If $\mathcal P^*(t)$ is a singleton for every $t\in(t^*-\varepsilon',t^*)$, for some $\varepsilon'>0$, then $(X^*,t^*)$ is a regular point, a non-differentiable point, a discontinuous isolated multiple point, a discontinuous non-isolated multiple point, a continuous bifurcation point, or an irregular accumulation point of $\mathcal P^*$.
--   2. The same holds for $\mathcal D^*$: let $Z^*\in\mathcal D^*(t^*)$. If $\mathcal D^*(t)$ is a singleton for every $t\in(t^*-\varepsilon',t^*)$, for some $\varepsilon'>0$, then $(Z^*,t^*)$ is a point of one of these six types of $\mathcal D^*$.
--
--   This is the main result of the paper, a complete local classification of the trajectory of solutions under merely continuous data. Irregular accumulation points are taken in the corrected sense of `IsIrregularAccumulationPoint`.
--
--   Differences from the source:
--   - correction: Definition 3.11, second bullet: times at which a continuous bifurcation (Definition 3.10) occurs → times at which RightContLossOfUniqueness holds: Definition 3.10 without its left condition; reason: the printed theorem is false. The LP min x₂ over x₁ + x₂ − s₁ = 1, x₁ − x₂ + s₂ = 1 + g(t), x₂ + s₃ = 1, x₁ + s₄ = 3, all variables ≥ 0, embedded in S⁶, with g(t) = t|sin(π/t)| for t > 0, g(t) = 0 for t ≤ 0, T = (−1, 1), satisfies Assumptions 3.1–3.3. Its P∗ is continuous everywhere, single-valued exactly on (−1, 0] ∪ {1/k}, and has no Definition 3.10 point, so t∗ = 0 is none of the six printed types. Example (P5t), p.23, uses the phrase in the corrected sense
--   - correction: Definition 3.11, first bullet: "At these times, either a discontinuous isolated multiple point or a discontinuous non-isolated multiple point appears" → not a condition; reason: read as a condition the theorem is false: add to the LP a block min h(t)u over u − v = 1, u + w = 2, u, v, w ≥ 0, with h(t) = |t| for t ≤ 0 and h(t) = t|sin(π/t)| for t > 0, and take g(t) = max(t, 0) in the LP above. Inner semicontinuity fails at every 1/k, and no 1/k is a Definition 3.7 or 3.8 point because the map is multi-valued just left of it. The proof never establishes the sentence
--   - encoding: P∗(t) is unique for every t ∈ (t∗ − ε′, t∗) → SingleValuedAt at every t of that interval that lies in T; reason: T is open, so ε′ can shrink; off T the data are unconstrained
--   - encoding: ε and the sequences of Definitions 3.4–3.11, implicitly in T → explicit interval ⊆ T clauses, and times s k ∈ T; reason: T is open and the sequences converge to t∗ ∈ T, so nothing is lost
--   - encoding: P∗(t) is differentiable at t∗ → MapDifferentiableAt: F s = {f s} near t∗, with f entrywise differentiable at t∗; reason: the unique-element function near t∗; entrywise differentiability is differentiability for any norm on matrices
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: ⟨C(t), X⟩ = p∗(t) and ⟨b(t), y⟩ = d∗(t) → minimality of X over Pfeas and maximality of y over dual feasible pairs; reason: the printed p∗ and d∗ are a min and a max, so being optimal is the same condition
--   - encoding: uniformly bounded norm of A(t) and of its pseudo-inverse → UniformBound: one constant M for both operator norms, Frobenius on Sⁿ and Euclidean on ℝᵐ; reason: all norms on finite-dimensional spaces are equivalent, so existence of a uniform bound does not depend on the choice
--   - encoding: sequences and continuity in Defs 2.11 and 2.12 → PKContinuousAt T, with times in T and the entrywise topology on matrices; reason: the printed definitions; the entrywise topology is the topology of every norm on matrices
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Theorem 3.15, p.15, with Definitions 3.4, 3.6, 3.7, 3.8, 3.10 and 3.11, pp.13–14

import Mathlib
import Definitions.Def_ParamSDPTraj_Popt
import Definitions.Def_ParamSDPTraj_Dopt
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_Assumption31
import Definitions.Def_ParamSDPTraj_Assumption32
import Definitions.Def_ParamSDPTraj_Assumption33
import Definitions.Def_ParamSDPTraj_IsRegularPoint
import Definitions.Def_ParamSDPTraj_IsNonDifferentiablePoint
import Definitions.Def_ParamSDPTraj_IsDiscIsolatedMultiplePoint
import Definitions.Def_ParamSDPTraj_IsDiscNonIsolatedMultiplePoint
import Definitions.Def_ParamSDPTraj_IsContinuousBifurcationPoint
import Definitions.Def_ParamSDPTraj_IsIrregularAccumulationPoint

namespace ParamSDPTraj

/-- **Theorem 3.15, Main result (corrected: irregular accumulation via right-sided continuous loss of uniqueness).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Theorem 3.15, p.15: "For a primal-dual pair of parametric SDPs (Pt, Dt), let Assumptions 3.1,
3.2, and 3.3 hold and consider a time t∗ ∈ T, X∗ ∈ P∗(t∗). If P∗(t) is unique for every
t ∈ (t∗ − ε′, t∗) for some ε′ > 0, then (X∗, t∗) must be a point of a type defined in Definitions
3.4, 3.6, 3.7, 3.8, 3.10, or 3.11. The same holds for D∗(t)".

**Formalization Note** As printed the theorem is false; `IsIrregularAccumulationPoint` carries the
correction. Counterexample: the LP min x₂ over x₁ + x₂ − s₁ = 1, x₁ − x₂ + s₂ = 1 + g(t),
x₂ + s₃ = 1, x₁ + s₄ = 3, all variables ≥ 0, embedded in S⁶, with g(t) = t|sin(π/t)| for t > 0 and
g(t) = 0 for t ≤ 0, on T = (−1, 1). Its P∗ is continuous everywhere, single-valued exactly on
(−1, 0] ∪ {1/k}, and has no Definition 3.10 point, so t∗ = 0 is none of the six printed types.
"Unique" is `SingleValuedAt`; continuity on the left is a consequence, not a hypothesis. -/
theorem theorem_3_15
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h31 : Assumption31 (Set.Ioo ti tf) A)
    (h32 : Assumption32 (Set.Ioo ti tf) A b C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C)
    (tstar : ℝ) (htstar : tstar ∈ Set.Ioo ti tf) :
    (∀ Xstar ∈ Popt A b C tstar,
      (∃ ε' > 0, ∀ t ∈ Set.Ioo (tstar - ε') tstar, t ∈ Set.Ioo ti tf →
        SingleValuedAt (Popt A b C) t) →
        IsRegularPoint (Set.Ioo ti tf) (Popt A b C) Xstar tstar ∨
        IsNonDifferentiablePoint (Set.Ioo ti tf) (Popt A b C) Xstar tstar ∨
        IsDiscIsolatedMultiplePoint (Set.Ioo ti tf) (Popt A b C) Xstar tstar ∨
        IsDiscNonIsolatedMultiplePoint (Set.Ioo ti tf) (Popt A b C) Xstar tstar ∨
        IsContinuousBifurcationPoint (Set.Ioo ti tf) (Popt A b C) Xstar tstar ∨
        IsIrregularAccumulationPoint (Set.Ioo ti tf) (Popt A b C) Xstar tstar) ∧
    (∀ Zstar ∈ Dopt A b C tstar,
      (∃ ε' > 0, ∀ t ∈ Set.Ioo (tstar - ε') tstar, t ∈ Set.Ioo ti tf →
        SingleValuedAt (Dopt A b C) t) →
        IsRegularPoint (Set.Ioo ti tf) (Dopt A b C) Zstar tstar ∨
        IsNonDifferentiablePoint (Set.Ioo ti tf) (Dopt A b C) Zstar tstar ∨
        IsDiscIsolatedMultiplePoint (Set.Ioo ti tf) (Dopt A b C) Zstar tstar ∨
        IsDiscNonIsolatedMultiplePoint (Set.Ioo ti tf) (Dopt A b C) Zstar tstar ∨
        IsContinuousBifurcationPoint (Set.Ioo ti tf) (Dopt A b C) Zstar tstar ∨
        IsIrregularAccumulationPoint (Set.Ioo ti tf) (Dopt A b C) Zstar tstar) := by sorry

end ParamSDPTraj
