-- Prove2me | Theorems.Thm_ParamSDPTraj_theorem_2_14
-- name    : ParamSDPTraj.theorem_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:15.520989+00:00
-- url     : https://prove2.me/theorems/c7bfda1a-4334-44f7-b15b-b203982526d0
-- title:
--   Theorem 2.14 (corrected: the dual half assumes LICQ) — $\mathcal P$ and $\mathcal D$ are outer semicontinuous
-- statement:
--   Let the data $A_i(t)$, $b(t)$, $C(t)$ be continuous on $T$. Then the primal feasible map $\mathcal P$ is outer semicontinuous at every $t\in T$. If moreover the matrices $A_i(t)$ are linearly independent for every $t\in T$, then the dual feasible map $\mathcal D$ is outer semicontinuous at every $t\in T$.
--
--   Together with Theorem 2.15 this gives continuity of both feasible maps.
--
--   Differences from the source:
--   - correction: D(t) is outer semi-continuous under continuous data alone → the dual half assumes LICQ on T; the primal half is as printed; reason: the printed dual half is false: for n = m = 1, A₁(t) = t, b = 0, C = 1, T = (−1, 1), D(t) = [0, ∞) for t ≠ 0 and D(0) = {1}, so 0 ∈ D(1/k) and 0 ∉ D(0). LICQ is part of Assumption 3.1
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: sequences and continuity in Defs 2.11 and 2.12 → PKContinuousAt T, with times in T and the entrywise topology on matrices; reason: the printed definitions; the entrywise topology is the topology of every norm on matrices
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Theorem 2.14, p.8

import Mathlib
import Definitions.Def_ParamSDPTraj_Pfeas
import Definitions.Def_ParamSDPTraj_Dfeas
import Definitions.Def_ParamSDPTraj_OuterSemicontAt
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_LICQ
import Definitions.Def_ParamSDPTraj_Assumption33

namespace ParamSDPTraj

/-- **Theorem 2.14 (corrected: the dual half assumes LICQ).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Theorem 2.14, p.8: "If A(t), b(t) and C(t) are continuous functions of t (see Assum. 3.3 in
Section 3), then the feasible set-valued maps P(t) and D(t) are outer semi-continuous at any
t ∈ T."

**Formalization Note** The primal half is as printed. The dual half as printed is false: for
n = m = 1, A₁(t) = t, b = 0, C = 1 on T = (−1, 1), D(t) = [0, ∞) for t ≠ 0 and D(0) = {1}, so
0 ∈ D(1/k) → 0 ∉ D(0). It assumes `LICQ` on T, which is part of Assumption 3.1. -/
theorem theorem_2_14
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C) :
    (∀ t ∈ Set.Ioo ti tf, OuterSemicontAt (Set.Ioo ti tf) (Pfeas A b) t) ∧
    (LICQ (Set.Ioo ti tf) A → ∀ t ∈ Set.Ioo ti tf, OuterSemicontAt (Set.Ioo ti tf) (Dfeas A C) t) := by sorry

end ParamSDPTraj
