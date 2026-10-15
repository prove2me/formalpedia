-- Prove2me | Theorems.Thm_SuspensionContract_ControlBand_lemma_EC_4
-- name    : SuspensionContract.ControlBand.lemma_EC_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:07.610097+00:00
-- url     : https://prove2.me/theorems/5ee30846-57ee-4198-99ba-a7f981a5fb0c
-- title:
--   Lemma EC.4, p. ec34 — under Condition 1, for each θ̲ ∈ (0, w̄) a unique (w̃(θ̲), C(θ̲)) with w̃(θ̲) ∈ (θ̲, w̄) satisfies (42)–(43) at θ̲
-- statement:
--   Assume the standing assumptions, Condition 1 and $K<\bar K_1$ (the standing case of Section EC.3.9.1). Then for every $\underline\theta\in(0,\bar w)$ there is exactly one pair $(\tilde w,C)$ with $\tilde w\in(\underline\theta,\bar w)$ such that
--   $$\mathcal V_{\tilde w}(\underline\theta)=V_C(\underline\theta)\quad\text{and}\quad \mathcal V_{\tilde w}'(\underline\theta)=V_C'(\underline\theta),$$
--   that is, value matching (42) and smooth pasting (43) hold at $\underline\vartheta=\underline\theta$ with $\tilde w$ in place of $\hat{\mathbf w}$ and $C$ in place of $\mathsf c$.
--
--   This is Step 1 of the construction of the control-band parameters: it defines $\tilde w(\underline\theta)$ and $C(\underline\theta)$.
--
--   **Formalization Note.** $\mathcal V'$ is the derivative within $\mathbb R_+$, two-sided at $\underline\theta>0$. The hypothesis $K<\bar K_1$ is the section's standing assumption; the lemma's conclusion does not involve $K$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec34, Lemma EC.4 (EC.3.9.1)

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction

namespace SuspensionContract.ControlBand

theorem lemma_EC_4 (P : Params) (hP : P.Standing) (h1 : P.Condition1) (hK : P.K < P.Kbar1) :
    ∀ θ ∈ Set.Ioo 0 P.wbar, ∃! p : ℝ × ℝ, P.MatchPair θ p := by sorry

end SuspensionContract.ControlBand
