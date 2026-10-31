-- Prove2me | Theorems.Thm_ParamSDPTraj_theorem_2_16
-- name    : ParamSDPTraj.theorem_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:04.366089+00:00
-- url     : https://prove2.me/theorems/54125882-caa2-478a-8595-b7a881d212de
-- title:
--   Theorem 2.16 — $\mathcal P^*$ and $\mathcal D^*$ are outer semicontinuous
-- statement:
--   Let the data $A_i(t)$, $b(t)$, $C(t)$ be continuous on $T$, and let the primal and dual feasible set-valued maps $\mathcal P$ and $\mathcal D$ be continuous on $T$. Then the optimal set-valued maps $\mathcal P^*$ and $\mathcal D^*$ are outer semicontinuous at every $t\in T$.
--
--   Consequently a discontinuity of an optimal map is always a loss of inner semicontinuity, which is how the classification of Section 3 counts discontinuities.
--
--   **Formalization Note** Neither LICQ nor strict feasibility is assumed, as printed.
--
--   Differences from the source:
--   - encoding: the primal and dual feasible set-valued maps are continuous → PKContinuousAt on T together with hPne and hDne: Pfeas t and Dfeas t are non-empty for every t ∈ T; reason: Definition 2.10 makes non-empty values part of being a set-valued map. Sequential continuity is vacuous for the empty map, and with P(t) empty on all of T the dual half fails, so the condition must be explicit
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: ⟨C(t), X⟩ = p∗(t) and ⟨b(t), y⟩ = d∗(t) → minimality of X over Pfeas and maximality of y over dual feasible pairs; reason: the printed p∗ and d∗ are a min and a max, so being optimal is the same condition
--   - encoding: sequences and continuity in Defs 2.11 and 2.12 → PKContinuousAt T, with times in T and the entrywise topology on matrices; reason: the printed definitions; the entrywise topology is the topology of every norm on matrices
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Theorem 2.16, p.9

import Mathlib
import Definitions.Def_ParamSDPTraj_Pfeas
import Definitions.Def_ParamSDPTraj_Dfeas
import Definitions.Def_ParamSDPTraj_Popt
import Definitions.Def_ParamSDPTraj_Dopt
import Definitions.Def_ParamSDPTraj_PKContinuousAt
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_Assumption33

namespace ParamSDPTraj

/-- **Theorem 2.16.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Theorem 2.16, p.9: "If A(t), b(t) and C(t) are continuous functions of t (see Assum. 3.3 in
Section 3) and the primal and dual feasible set-valued maps are continuous, then the optimal
set-valued maps P∗(t) and D∗(t) are outer semi-continuous at any t ∈ T."

**Formalization Note** No LICQ and no strict feasibility, as printed. `hPne`, `hDne` state what
"set-valued map" means in Definition 2.10, p.7: the values are non-empty. They are needed: with
empty primal values the dual half fails. -/
theorem theorem_2_16
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C)
    (hPne : ∀ t ∈ Set.Ioo ti tf, (Pfeas A b t).Nonempty)
    (hDne : ∀ t ∈ Set.Ioo ti tf, (Dfeas A C t).Nonempty)
    (hP : ∀ t ∈ Set.Ioo ti tf, PKContinuousAt (Set.Ioo ti tf) (Pfeas A b) t)
    (hD : ∀ t ∈ Set.Ioo ti tf, PKContinuousAt (Set.Ioo ti tf) (Dfeas A C) t) :
    ∀ t ∈ Set.Ioo ti tf,
      OuterSemicontAt (Set.Ioo ti tf) (Popt A b C) t ∧ OuterSemicontAt (Set.Ioo ti tf) (Dopt A b C) t := by sorry

end ParamSDPTraj
