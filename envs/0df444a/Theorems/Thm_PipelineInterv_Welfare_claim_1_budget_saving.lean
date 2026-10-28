-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_claim_1_budget_saving
-- name    : PipelineInterv.Welfare.claim_1_budget_saving
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:07.608409+00:00
-- url     : https://prove2.me/theorems/bec203cf-9441-44b9-bda1-9a176667aeb6
-- title:
--   Proof of Claim 1, App. A.1, pp. 24–25 — trimming ε of intervention costs at most ‖R‖∞ε of reward
-- statement:
--   Fix an instance of the pipeline intervention problem satisfying the standing assumptions of §2, a transition $t$ and $\varepsilon>0$. Let $M^*_t$ be a left stochastic matrix that agrees with $M^0_t$ on every non-malleable entry. Then there is a left stochastic matrix $M^\varepsilon_t$, also agreeing with $M^0_t$ on every non-malleable entry, such that
--   $$c(M^\varepsilon_t,M^0_t)=\max\bigl(0,\ c(M^*_t,M^0_t)-\varepsilon\bigr),$$
--   and such that for every vector $r\in\mathbb R^w$ with $0\le r(v)\le\rho$ for all $v$ and every distribution $D\in\mathcal D$,
--   $$r^\top M^\varepsilon_t D\ \ge\ r^\top M^*_t D-\rho\,\varepsilon .$$
--
--   In the paper $\rho=\|R\|_\infty$ and $r^\top=R^\top M_{k-1}\cdots M_{t+1}$ is the reward-to-go after transition $t$. The matrix $M^\varepsilon_t$ saves $\varepsilon$ of intervention budget (or all of it) at a cost of at most $\|R\|_\infty\varepsilon$ in expected reward; this is the construction behind Claim 1.
--
--   **Formalization Note.** The vector $r$ and the bound $\rho$ are quantified universally rather than fixed to the paper's $R_{t+1}$ and $\|R\|_\infty$; the paper uses only $0\le R_{t+1}\le\|R\|_\infty$. The page prints the sign condition as "$M^\varepsilon_t(u,v)\ge M^0_t(u,v)$" (index swap) and the first display as "$R^\top_{t+1}M_tD_{t,j}$" for $M^\varepsilon_t$; both are read as typos.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, pp. 24–25, proof of Claim 1 (Appendix A.1), construction of M^ε_t and the displays for c(M^ε_t, M⁰_t) and R⊤_{t+1}M^ε_t D_{t,j}

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem claim_1_budget_saving {w K : ℕ} (I : Instance w K) (hI : I.Standing) (t : Fin K)
    (Mstar : Matrix (Fin w) (Fin w) ℝ) (hMstar : Mstar ∈ colStochastic ℝ (Fin w))
    (hResp : Respects I t Mstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ Meps : Matrix (Fin w) (Fin w) ℝ, Meps ∈ colStochastic ℝ (Fin w) ∧ Respects I t Meps ∧
      cost Meps (I.M0 t) = max 0 (cost Mstar (I.M0 t) - ε) ∧
      ∀ (r D : Fin w → ℝ) (ρ : ℝ), (∀ v, 0 ≤ r v ∧ r v ≤ ρ) → IsDist D →
        r ⬝ᵥ (Mstar *ᵥ D) - ρ * ε ≤ r ⬝ᵥ (Meps *ᵥ D) := by sorry

end PipelineInterv.Welfare
