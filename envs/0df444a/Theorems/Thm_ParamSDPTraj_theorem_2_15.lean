-- Prove2me | Theorems.Thm_ParamSDPTraj_theorem_2_15
-- name    : ParamSDPTraj.theorem_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:18.7596+00:00
-- url     : https://prove2.me/theorems/30791b05-1c69-4b75-a2f4-3d5feef971c9
-- title:
--   Theorem 2.15 — $\mathcal P$ and $\mathcal D$ are inner semicontinuous
-- statement:
--   Assume that strict feasibility holds at every $t\in T$, that $\mathcal A(t)$ is surjective for every $t\in T$, that the norms of $\mathcal A(t)$ and of its pseudo-inverse $\mathcal A^*(t)(\mathcal A(t)\mathcal A^*(t))^{-1}$ are uniformly bounded in $t$, and that $A_i(t)$, $b(t)$, $C(t)$ are continuous. Then the feasible maps $\mathcal P$ and $\mathcal D$ are inner semicontinuous at every $t\in T$.
--
--   The paper presents the primal case, with $\mathcal A(t)$ time-dependent, as an original contribution.
--
--   Differences from the source:
--   - encoding: A(t) is surjective for every t ∈ T → LICQ inside Assumption31: linear independence of the A_i(t); reason: for symmetric A_i(t) these are the same condition, as Assumption 3.1 says
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: uniformly bounded norm of A(t) and of its pseudo-inverse → UniformBound: one constant M for both operator norms, Frobenius on Sⁿ and Euclidean on ℝᵐ; reason: all norms on finite-dimensional spaces are equivalent, so existence of a uniform bound does not depend on the choice
--   - encoding: sequences and continuity in Defs 2.11 and 2.12 → PKContinuousAt T, with times in T and the entrywise topology on matrices; reason: the printed definitions; the entrywise topology is the topology of every norm on matrices
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Theorem 2.15, p.8

import Mathlib
import Definitions.Def_ParamSDPTraj_Pfeas
import Definitions.Def_ParamSDPTraj_Dfeas
import Definitions.Def_ParamSDPTraj_InnerSemicontAt
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_Assumption31
import Definitions.Def_ParamSDPTraj_Assumption32
import Definitions.Def_ParamSDPTraj_Assumption33

namespace ParamSDPTraj

/-- **Theorem 2.15.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Theorem 2.15, p.8: "Assume that strict feasibility holds at any t ∈ T (see Assum. 3.2 in
Section 3), that the linear operator A(t) is surjective for every t ∈ T, that the norm of A(t)
and the norm of its pseudo-inverse A∗(t)(A(t)A∗(t))−1 are uniformly bounded in t (see Assum. 3.1
in Section 3), and that A(t), b(t) and C(t) are continuous functions of t (see Assum. 3.3 in
Section 3). Then the set-valued maps P(t) and D(t) are inner semi-continuous for every t ∈ T."
 -/
theorem theorem_2_15
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h31 : Assumption31 (Set.Ioo ti tf) A)
    (h32 : Assumption32 (Set.Ioo ti tf) A b C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C) :
    ∀ t ∈ Set.Ioo ti tf,
      InnerSemicontAt (Set.Ioo ti tf) (Pfeas A b) t ∧ InnerSemicontAt (Set.Ioo ti tf) (Dfeas A C) t := by sorry

end ParamSDPTraj
