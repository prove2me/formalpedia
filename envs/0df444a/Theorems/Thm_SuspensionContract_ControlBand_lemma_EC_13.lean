-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_lemma_EC_13
-- name    : SuspensionContract.ControlBand.lemma_EC_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:24.575385+00:00
-- url     : https://prove2.me/theorems/24a8753e-5e60-49d9-9c7d-78beda168015
-- title:
--   Lemma EC.13, p. ec42 — under Condition 3, at the constructed control-band tuple (𝒜_I V_I)(w) ≥ 0 for w ∈ (0, ϑ̲)
-- statement:
--   Assume the standing assumptions and Condition 3, with $\underline\vartheta\in(0,\underline\theta^0)$ in the case Condition 1 and $K<\bar K_1$, or $\underline\vartheta\in(\breve{\underline\theta},\underline\theta^0)$ in the case Condition 2 and $K<\underline K$. Let $\underline\vartheta$ satisfy $\psi(\underline\vartheta)=K$, and let $\mathsf c=C(\underline\vartheta)$, $\hat{\mathbf w}=\tilde w(\underline\vartheta)$. With $V_I$ defined by (46) from these parameters ($V_I=V_{\mathsf c}$ on $[0,\underline\vartheta)$ and $\mathcal V_{\hat{\mathbf w}}$ beyond),
--   $$(\mathcal A_IV_I)(w)\ge0\qquad\text{for all }w\in(0,\underline\vartheta).$$
--
--   This is the hardest part of the optimality condition (20): on the suspension region the working-state operator mixes $V_{\mathsf c}(w)$ with the look-ahead value $V_I(w+\beta)$.
--
--   **Formalization Note.** The paper states the inequality on $[0,\underline\vartheta)$; it is posed on $(0,\underline\vartheta)$ because the left derivative does not exist at $0$ and $V_{\mathsf c}'(0^+)=+\infty$ (the mission-wide convention for (20)). Both branches of Condition 3 and the constructed tuple are used as for Lemma EC.12.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec42, Lemma EC.13 (EC.3.10); proof EC.3.12

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction

namespace SuspensionContract.ControlBand

theorem lemma_EC_13 (P : Params) (hP : P.Standing) (th : ℝ)
    (hcase : (P.Condition1 ∧ P.K < P.Kbar1 ∧ th ∈ Set.Ioo 0 P.theta0) ∨
      (P.Condition2 ∧ P.K < P.Klow ∧ th ∈ Set.Ioo P.thetaBreve P.theta0C2))
    (hψ : P.psi th = P.K) :
    ∀ w ∈ Set.Ioo 0 th, 0 ≤ P.AI (P.VI46 (P.Cof th) (P.wtil th) th) w := by sorry

end SuspensionContract.ControlBand
