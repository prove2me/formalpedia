-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_EC3_10_case1_AI
-- name    : SuspensionContract.ControlBand.EC3_10_case1_AI
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T22:25:14.425679+00:00
-- url     : https://prove2.me/theorems/780cc4b6-0f8b-49ca-b2fd-8f9ec949ca43
-- title:
--   EC.3.10, Case 1, (EC.79), p. ec41 — $(\mathcal A_IV_I)(w)\ge0$ on $[\underline\vartheta,\hat{\mathbf w})$
-- statement:
--   Assume the standing assumptions and Condition 3, in either of its two cases: (a) Condition 1, $K<\bar K_1$ and $\underline\vartheta\in(0,\underline\theta^0)$ (Lemma EC.7), or (b) Condition 2, $K<\underline K$ and $\underline\vartheta\in(\breve{\underline\theta},\underline\theta^0)$ (Lemmas EC.9, EC.11). Let $\underline\vartheta$ satisfy $\psi(\underline\vartheta)=K$ ($\psi$ of (EC.75)), and let $\mathsf c=C(\underline\vartheta)$, $\hat{\mathbf w}=\tilde w(\underline\vartheta)$ (Lemmas EC.4/EC.8) and $\bar\vartheta=\bar\theta(\underline\vartheta)$ ((EC.74)) be the parameters built from it in EC.3.9. Let $V_I,V_\emptyset$ be the control-band functions (46) built from $(\mathsf c,\hat{\mathbf w},\bar\vartheta,\underline\vartheta)$: $V_I=V_{\mathsf c}$ on $[0,\underline\vartheta)$ and $\mathcal V_{\hat{\mathbf w}}$ beyond; $V_\emptyset=V_{\mathsf c}$ on $[0,\bar\vartheta)$ and $\mathcal V_{\hat{\mathbf w}}-K$ beyond. Then
--
--   $$(\mathcal A_IV_I)(w)\ge0\qquad\text{for all }w\in[\underline\vartheta,\hat{\mathbf w}).\qquad\text{(EC.79)}$$
--
--   This is Case 1 of the proof of Proposition 7: on the working region of the band, $V_I=\mathcal V_{\hat{\mathbf w}}$; on $[\check w(\hat{\mathbf w}),\hat{\mathbf w})$ the delay ODE gives equality, and on the linear piece $[\underline\vartheta,\check w(\hat{\mathbf w}))$ of the concavified function the inequality follows from concavity.
--
--   **Formalization Note.** The hypotheses mirror those of the milestones `lemma_EC_12` / `lemma_EC_13` ("the conditions stated in Proposition 7", read as Condition 3 together with the tuple constructed in EC.3.9); the paper writes out the Condition 1 branch and states that the Condition 2 branch is the same. $\mathcal A_I,\mathcal A_\emptyset$ use the left derivative (`derivWithin` on $(-\infty,w]$).
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (https://people.duke.edu/~psun/bio/OptSwitching.pdf), p. ec41, Section EC.3.10 (Proof of Proposition 7), Case 1, inequality (EC.79)

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction

namespace SuspensionContract.ControlBand

theorem EC3_10_case1_AI (P : Params) (hP : P.Standing) (th : ℝ)
    (hcase : (P.Condition1 ∧ P.K < P.Kbar1 ∧ th ∈ Set.Ioo 0 P.theta0) ∨
      (P.Condition2 ∧ P.K < P.Klow ∧ th ∈ Set.Ioo P.thetaBreve P.theta0C2))
    (hψ : P.psi th = P.K) :
    ∀ w ∈ Set.Ico th (P.wtil th), 0 ≤ P.AI (P.VI46 (P.Cof th) (P.wtil th) th) w := by sorry

end SuspensionContract.ControlBand
