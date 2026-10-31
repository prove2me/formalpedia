-- Prove2me | Theorems.Thm_ParamSDPTraj_optimal_sets_nonempty_bounded
-- name    : ParamSDPTraj.optimal_sets_nonempty_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:35.3959+00:00
-- url     : https://prove2.me/theorems/cadeeef8-6178-4b2b-aff4-5132d2ca00b5
-- title:
--   §3, p.12, second bullet — $\mathcal P^*(t)$, $\mathcal D^*(t)$ are non-empty and bounded
-- statement:
--   Under Assumptions 3.1, 3.2 and 3.3 on $T$, for every $t\in T$ the primal and dual optimal sets $\mathcal P^*(t)$ and $\mathcal D^*(t)$ are non-empty and bounded.
--
--   This is what makes the case split of Theorem 3.15 exhaustive: at every time the optimal map is either single-valued or multi-valued, never empty.
--
--   Differences from the source:
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: ⟨C(t), X⟩ = p∗(t) and ⟨b(t), y⟩ = d∗(t) → minimality of X over Pfeas and maximality of y over dual feasible pairs; reason: the printed p∗ and d∗ are a min and a max, so being optimal is the same condition
--   - encoding: uniformly bounded norm of A(t) and of its pseudo-inverse → UniformBound: one constant M for both operator norms, Frobenius on Sⁿ and Euclidean on ℝᵐ; reason: all norms on finite-dimensional spaces are equivalent, so existence of a uniform bound does not depend on the choice
--   - encoding: bounded → a Frobenius bound ∃ R, ∀ X, frob X ≤ R; reason: Lean has no global bornology on Matrix; all norms are equivalent
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §3, p.12, second bullet

import Mathlib
import Definitions.Def_ParamSDPTraj_Popt
import Definitions.Def_ParamSDPTraj_Dopt
import Definitions.Def_ParamSDPTraj_frob
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_Assumption31
import Definitions.Def_ParamSDPTraj_Assumption32
import Definitions.Def_ParamSDPTraj_Assumption33

namespace ParamSDPTraj

/-- **§3, second bullet: optimal sets non-empty and bounded.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §3, p.12: "Summarizing, Assumptions 3.1, 3.2, and 3.3 ensure that: … The primal and dual
optimal faces P∗(t), D∗(t) are non-empty and bounded for all t ∈ T."

**Formalization Note** Boundedness is a Frobenius bound; `Matrix` has no global bornology. -/
theorem optimal_sets_nonempty_bounded
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h31 : Assumption31 (Set.Ioo ti tf) A)
    (h32 : Assumption32 (Set.Ioo ti tf) A b C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C) :
    ∀ t ∈ Set.Ioo ti tf,
      (Popt A b C t).Nonempty ∧ (∃ R : ℝ, ∀ X ∈ Popt A b C t, frob X ≤ R) ∧
      (Dopt A b C t).Nonempty ∧ (∃ R : ℝ, ∀ Z ∈ Dopt A b C t, frob Z ≤ R) := by sorry

end ParamSDPTraj
