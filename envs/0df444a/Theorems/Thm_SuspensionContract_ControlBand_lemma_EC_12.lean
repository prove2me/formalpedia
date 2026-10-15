-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_lemma_EC_12
-- name    : SuspensionContract.ControlBand.lemma_EC_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:16.275023+00:00
-- url     : https://prove2.me/theorems/7f8812a1-ee2c-4498-960c-0e46503dae7e
-- title:
--   Lemma EC.12, p. ec42 — under Condition 3, at the constructed control-band tuple (𝒜_∅V_∅)(w) ≥ 0 for w ∈ [ϑ̄, 𝐰̂)
-- statement:
--   Assume the standing assumptions and Condition 3, in either of its two cases: Condition 1, $K<\bar K_1$ and $\underline\vartheta\in(0,\underline\theta^0)$ (the interval of Lemma EC.7), or Condition 2, $K<\underline K$ and $\underline\vartheta\in(\breve{\underline\theta},\underline\theta^0)$ (the interval of Lemma EC.11, with $\underline\theta^0$ of Lemma EC.9). Let $\underline\vartheta$ satisfy $\psi(\underline\vartheta)=K$ (the unique root of Lemma EC.7, resp. EC.11), and let $\mathsf c=C(\underline\vartheta)$, $\hat{\mathbf w}=\tilde w(\underline\vartheta)$, $\bar\vartheta=\bar\theta(\underline\vartheta)$ be the parameters built from it in EC.3.9. With $V_\emptyset$ defined by (46) from these parameters,
--   $$(\mathcal A_\emptyset V_\emptyset)(w)\ge0\qquad\text{for all }w\in[\bar\vartheta,\hat{\mathbf w}).$$
--
--   This is the part of the optimality condition (20) for the suspension state on the upper part of the band, where $V_\emptyset=\mathcal V_{\hat{\mathbf w}}-K$.
--
--   **Formalization Note.** "The conditions stated in Proposition 7" are read as Condition 3 together with the tuple constructed in EC.3.9; both branches of Condition 3 are posed, as the lemma claims (the paper's proof writes out the Condition 1 branch and states that the Condition 2 branch is the same, EC.3.10). Under Condition 2, $\check w\equiv0$, so $\mathcal V_{\tilde w}=V_{\tilde w}$ and the same Lean objects apply. $\mathcal A_\emptyset$ uses the left derivative.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec42, Lemma EC.12 (EC.3.10)

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction

namespace SuspensionContract.ControlBand

theorem lemma_EC_12 (P : Params) (hP : P.Standing) (th : ℝ)
    (hcase : (P.Condition1 ∧ P.K < P.Kbar1 ∧ th ∈ Set.Ioo 0 P.theta0) ∨
      (P.Condition2 ∧ P.K < P.Klow ∧ th ∈ Set.Ioo P.thetaBreve P.theta0C2))
    (hψ : P.psi th = P.K) :
    ∀ w ∈ Set.Ico (P.thetaBar th) (P.wtil th),
      0 ≤ P.A0 (P.V046 (P.Cof th) (P.wtil th) (P.thetaBar th)) w := by sorry

end SuspensionContract.ControlBand
