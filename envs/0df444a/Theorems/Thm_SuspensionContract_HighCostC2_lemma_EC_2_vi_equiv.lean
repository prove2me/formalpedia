-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_lemma_EC_2_vi_equiv
-- name    : SuspensionContract.HighCostC2.lemma_EC_2_vi_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:28.954031+00:00
-- url     : https://prove2.me/theorems/7bb2c12f-396d-4fc6-a58a-fb88737a3e16
-- title:
--   Lemma EC.2(vi), second claim, p. ec23 — if ρ > r + µ, then V̄ − (ρ − r)w̄/(ρ − r − µ) ≥ v̲ ⟺ R ≥ R̂
-- statement:
--   Assume the standing assumptions of the model (in particular $0<r\le\rho$, $0\le\underline\mu<\mu$, $0<b\le c$, $R\Delta\mu>c$), and suppose the agent is much more impatient than the principal in the sense that $\rho>r+\mu$. Then, with $\bar V$ from (10), $\bar w=\beta\mu/\rho$ from (9), $\underline v=\underline\mu R/r$ from (8) and $\hat R$ from (28),
--   $$\bar V-\frac{\rho-r}{\rho-r-\mu}\,\bar w\ \ge\ \underline v\quad\Longleftrightarrow\quad R\ge\hat R .$$
--
--   The left-hand side is the value at $w=0$ of the limit, as $\tilde w\uparrow\bar w$, of the delay-ODE solutions $V_{\tilde w}$; the equivalence says that this limit lies above the outside value $\underline v$ exactly when the revenue condition of Condition 2 holds. In the proof of Proposition 4 it is what makes the linear $V_I$ of (31) satisfy $(\mathcal A_IV_I)\ge0$ on $[0,\bar w]$.
--
--   **Formalization Note.** Only the second claim ("Furthermore, …") of item (vi) is stated; the limit claim needs the delay-ODE family $V_{\tilde w}$, which this mission does not define.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec23, Lemma EC.2(vi), second claim

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting

namespace SuspensionContract.HighCostC2
theorem lemma_EC_2_vi_equiv (P : Params) (hP : P.Standing) (hρ : P.r + P.μ < P.ρ) :
    P.vlow ≤ P.Vbar - (P.ρ - P.r) / (P.ρ - P.r - P.μ) * P.wbar ↔ P.Rhat ≤ P.R := by sorry
end SuspensionContract.HighCostC2
