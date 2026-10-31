-- Prove2me | Theorems.Thm_ParamSDPTraj_lemma_2_18
-- name    : ParamSDPTraj.lemma_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:25.319164+00:00
-- url     : https://prove2.me/theorems/20c36213-3841-4b60-9db6-e65b50c725a2
-- title:
--   Lemma 2.18 (corrected: assumes LICQ; read with $\delta>0$) — $\mathcal P^*$ and $\mathcal D^*$ are locally uniformly bounded
-- statement:
--   Assume that strict feasibility holds at every $t\in T$, that $A_i(t)$, $b(t)$, $C(t)$ are continuous on $T$, and that the matrices $A_i(t)$ are linearly independent for every $t\in T$. Then $\mathcal P^*$ and $\mathcal D^*$ are locally uniformly bounded: for every $t\in T$ there are compact sets $C_p$, $C_d$ and $\delta>0$ with $[t-\delta,t+\delta]\subseteq T$ such that
--
--   $$\mathcal P^*(s)\subseteq C_p\quad\text{and}\quad\mathcal D^*(s)\subseteq C_d\qquad\text{for all }s\in[t-\delta,t+\delta].$$
--
--   This is the compactness input to Proposition 2.19.
--
--   Differences from the source:
--   - reading: δ ≥ 0 → δ > 0 with [t − δ, t + δ] ⊆ T; reason: δ = 0 says only that P∗(t) and D∗(t) are bounded, which is not the "locally uniformly bounded" the sentence defines
--   - correction: strict feasibility and continuous data suffice → also assumes LICQ on T; reason: the printed hypotheses do not suffice: for n = m = 1, A₁(t) = t, b(t) = sign(t)√|t|, C = 1, T = (−1, 1), both problems are strictly feasible, the data are continuous, and P∗(t) = {1/√|t|} is unbounded near 0. LICQ is part of Assumption 3.1
--   - encoding: A_i(t), C(t) ∈ Sⁿ → A_i, C are functions into all square matrices, with the hypothesis SymmetricData on T; reason: the same objects; the data off T are unconstrained and do not enter
--   - encoding: the dual map D(t), D∗(t) as printed with A∗(t)[X] and a free y → Dfeas, Dopt are sets of Z with an existentially quantified y; reason: the page's A∗(t)[X] is a slip for A∗(t)[y], and Remark 2.1 refers to a dual point as a matrix Z
--   - encoding: ⟨C(t), X⟩ = p∗(t) and ⟨b(t), y⟩ = d∗(t) → minimality of X over Pfeas and maximality of y over dual feasible pairs; reason: the printed p∗ and d∗ are a min and a max, so being optimal is the same condition
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Lemma 2.18, p.9

import Mathlib
import Definitions.Def_ParamSDPTraj_Popt
import Definitions.Def_ParamSDPTraj_Dopt
import Definitions.Def_ParamSDPTraj_SymmetricData
import Definitions.Def_ParamSDPTraj_LICQ
import Definitions.Def_ParamSDPTraj_Assumption32
import Definitions.Def_ParamSDPTraj_Assumption33

namespace ParamSDPTraj

/-- **Lemma 2.18 (read with δ > 0; corrected: assumes LICQ).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Lemma 2.18, p.9: "Assume that strict feasibility holds at any t ∈ T (see Assum. 3.2 in
Section 3) and that A(t), b(t) and C(t) are continuous functions of t (see Assum. 3.3 in
Section 3), then P∗(t) and D∗(t) are locally uniformly bounded at any t ∈ T, i.e., for every
t ∈ T there exists compact sets Cp, Cd and δ ≥ 0 such that P∗(s) ⊆ Cp and D∗(s) ⊆ Cd for all
s ∈ [t − δ, t + δ]."

**Formalization Note** "δ ≥ 0" is read as δ > 0 with [t − δ, t + δ] ⊆ T: δ = 0 says only that P∗(t)
and D∗(t) are bounded, not "locally uniformly bounded". Under that reading LICQ is needed: for
n = m = 1, A₁(t) = t, b(t) = sign(t)√|t|, C = 1 on T = (−1, 1), both problems are strictly
feasible, the data are continuous, and P∗(t) = {1/√|t|} is unbounded near 0. -/
theorem lemma_2_18
    {n m : ℕ} {ti tf : ℝ}
    (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : SymmetricData (Set.Ioo ti tf) A C)
    (h32 : Assumption32 (Set.Ioo ti tf) A b C)
    (h33 : Assumption33 (Set.Ioo ti tf) A b C)
    (hLICQ : LICQ (Set.Ioo ti tf) A) :
    ∀ t ∈ Set.Ioo ti tf, ∃ Cp Cd : Set (Matrix (Fin n) (Fin n) ℝ), IsCompact Cp ∧ IsCompact Cd ∧
      ∃ δ > 0, Set.Icc (t - δ) (t + δ) ⊆ Set.Ioo ti tf ∧
        ∀ s ∈ Set.Icc (t - δ) (t + δ), Popt A b C s ⊆ Cp ∧ Dopt A b C s ⊆ Cd := by sorry

end ParamSDPTraj
