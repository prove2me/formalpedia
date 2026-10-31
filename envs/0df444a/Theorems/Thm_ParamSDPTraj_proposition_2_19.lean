-- Prove2me | Theorems.Thm_ParamSDPTraj_proposition_2_19
-- name    : ParamSDPTraj.proposition_2_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:01.476994+00:00
-- url     : https://prove2.me/theorems/60798519-92dc-4e0a-96fa-65defc6e5a0d
-- title:
--   Proposition 2.19 (corrected: assumes LICQ) — a single-valued optimal map is continuous
-- statement:
--   Assume that strict feasibility holds at every $t\in T$, that $A_i(t)$, $b(t)$, $C(t)$ are continuous on $T$, and that the matrices $A_i(t)$ are linearly independent for every $t\in T$. Let $\hat t\in T$. If $\mathcal P^*$ is single-valued at $\hat t$, then $\mathcal P^*$ is continuous at $\hat t$. The same holds for $\mathcal D^*$.
--
--   This is why the left-neighbourhood hypothesis of Theorem 3.15 needs only uniqueness: continuity on the left is then automatic.
--
--   Differences from the source:
--   - correction: strict feasibility and continuous data suffice → also assumes LICQ on T; reason: as printed the statement is false: for n = m = 1, A₁(t) = t, b(t) = t, C = 1, T = (−1, 1), both problems are strictly feasible and the data are continuous, while P∗(t) = {1} for t ≠ 0 and P∗(0) = {0}. LICQ is part of Assumption 3.1
--   - encoding: so that by Lemma 2.18 P∗(t) and D∗(t) are locally uniformly bounded at any t ∈ T → not a hypothesis; reason: the clause is the paper's justification and states a consequence
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: ⟨C(t), X⟩ = p∗(t) and ⟨b(t), y⟩ = d∗(t) → minimality of X over Pfeas and maximality of y over dual feasible pairs; reason: the printed p∗ and d∗ are a min and a max, so being optimal is the same condition
--   - encoding: sequences and continuity in Defs 2.11 and 2.12 → PKContinuousAt T, with times in T and the entrywise topology on matrices; reason: the printed definitions; the entrywise topology is the topology of every norm on matrices
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Proposition 2.19, p.9

import Mathlib
import Definitions.Def_ParamSDPTraj_Popt
import Definitions.Def_ParamSDPTraj_Dopt
import Definitions.Def_ParamSDPTraj_SingleValuedAt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_LICQ
import Definitions.Def_ParamSDPTraj_Assumption32
import Definitions.Def_ParamSDPTraj_Assumption33

namespace ParamSDPTraj

/-- **Proposition 2.19 (corrected: assumes LICQ).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Proposition 2.19, p.9: "Assume that strict feasibility holds at any t ∈ T (see Assum. 3.2 in
Section 3), so that by Lemma 2.18 P∗(t) and D∗(t) are locally uniformly bounded at any t ∈ T, and
that A(t), b(t) and C(t) are continuous functions of t (see Assum. 3.3 in Section 3). If P∗(t) is
single-valued at t̂, then P∗(t) is continuous at t̂. The same holds for D∗(t)."

**Formalization Note** The clause "so that by Lemma 2.18 …" is the paper's justification, not a
hypothesis. As printed the statement is false: for n = m = 1, A₁(t) = t, b(t) = t, C = 1 on
T = (−1, 1), both problems are strictly feasible, P∗(t) = {1} for t ≠ 0 and P∗(0) = {0}.
`hLICQ` is the correction; it is part of Assumption 3.1. -/
theorem proposition_2_19
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h32 : Assumption32 (Set.Ioo ti tf) A b C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C)
    (hLICQ : LICQ (Set.Ioo ti tf) A)
    (that : ℝ) (hthat : that ∈ Set.Ioo ti tf) :
    (SingleValuedAt (Popt A b C) that → PKContinuousAt (Set.Ioo ti tf) (Popt A b C) that) ∧
    (SingleValuedAt (Dopt A b C) that → PKContinuousAt (Set.Ioo ti tf) (Dopt A b C) that) := by sorry

end ParamSDPTraj
