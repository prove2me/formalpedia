-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_EC3_9_construction
-- name    : SuspensionContract.ControlBand.EC3_9_construction
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T22:25:15.051871+00:00
-- url     : https://prove2.me/theorems/15d97abc-1a58-4ae7-b57f-14a82d6df516
-- title:
--   EC.3.9, pp. ec37–ec40 — the root $\underline\vartheta$ of $\psi=K$ and its constructed tuple satisfy Proposition 6
-- statement:
--   Assume the standing assumptions and Condition 3 (either Condition 1 and $K<\bar K_1$, or Condition 2 and $K<\underline K$). Then there is a number $\underline\vartheta$ such that
--
--   1. in the Condition 1 case $\underline\vartheta\in(0,\underline\theta^0)$ (with $\underline\theta^0$ of Lemma EC.5), and in the Condition 2 case $\underline\vartheta\in(\breve{\underline\theta},\underline\theta^0)$ (with $\breve{\underline\theta}$ of EC.3.9.2 and $\underline\theta^0$ of Lemma EC.9);
--   2. $\psi(\underline\vartheta)=K$, where $\psi$ is defined in (EC.75);
--   3. the quadruple
--   $$\hat{\mathbf w}=\tilde w(\underline\vartheta),\qquad \mathsf c=C(\underline\vartheta),\qquad \bar\vartheta=\bar\theta(\underline\vartheta),\qquad \underline\vartheta$$
--   (with $\tilde w,C$ of Lemmas EC.4/EC.8 and $\bar\theta$ of (EC.74)) satisfies all conclusions of Proposition 6: $\mathsf c>0$, $0<\underline\vartheta<\bar\vartheta<\hat{\mathbf w}$, $\hat{\mathbf w}<\hat{\mathrm w}$ under Condition 1 and $\hat{\mathbf w}<\bar w$ under Condition 2, value matching and smooth pasting (42)–(45), and $\bar\vartheta>\check w(\hat{\mathbf w})$.
--
--   This is the content of the proof of Proposition 6 (EC.3.9.1 for Condition 1: "there exists a unique $\underline\vartheta\in(0,\underline\theta^0)$ such that $\psi(\underline\vartheta)=K$ … the quadruple … satisfies (42)–(45)"; EC.3.9.2 for Condition 2). It records not only that a Proposition 6 tuple exists, but which tuple the paper builds, which is what the proof of Proposition 7 (EC.3.10–EC.3.12) works with.
--
--   **Formalization Note.** The conclusions of Proposition 6 are the definition `Prop6Params`; the interval conditions on $\underline\vartheta$ are exactly the hypotheses of the milestones `lemma_EC_12` and `lemma_EC_13`.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (https://people.duke.edu/~psun/bio/OptSwitching.pdf), pp. ec37–ec40, Section EC.3.9 (end of EC.3.9.1, p. ec38: the quadruple defined by ŵ = w̃(ϑ̲), c = C(ϑ̲), ϑ̄ = θ̄(ϑ̲) satisfies (42)–(45); EC.3.9.2, p. ec40); Lemmas EC.4–EC.11; Proposition 6, p. 26

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction

namespace SuspensionContract.ControlBand

theorem EC3_9_construction (P : Params) (hP : P.Standing) (h3 : P.Condition3) :
    ∃ th : ℝ, ((P.Condition1 ∧ P.K < P.Kbar1 ∧ th ∈ Set.Ioo 0 P.theta0) ∨
      (P.Condition2 ∧ P.K < P.Klow ∧ th ∈ Set.Ioo P.thetaBreve P.theta0C2)) ∧
      P.psi th = P.K ∧ P.Prop6Params (P.Cof th) (P.wtil th) (P.thetaBar th) th := by sorry

end SuspensionContract.ControlBand
