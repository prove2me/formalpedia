-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_tau0_step
-- name    : TiltingFTT.Optimal.tau0_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:48.452377+00:00
-- url     : https://prove2.me/theorems/ac9fda9f-7573-4657-811c-c0413fb2c312
-- title:
--   Proof of Proposition 6, p. 47 — ΔW = W_S − W_P > 0 iff τ < τ_0 on [0, τ_FB], with ΔW(τ_0) = 0
-- statement:
--   Assume the standing assumptions and specification (23) with $v>0$. Compare the Pareto-optimal separating welfare $W_S(\tau)=W^*-(1-\beta)(\delta_I-\delta_U)(1-\bar T_L(\tau))F_L$ with the Pareto-optimal pooling welfare $W_P$ (trade $T_P=1$). Then:
--
--   1. for every $\tau\in[0,\tau_{FB}]$, $$W_P<W_S(\tau)\iff\tau<\tau_0;$$
--   2. if $0\le\tau_0\le\tau_{FB}$, then $W_S(\tau_0)=W_P$.
--
--   Here $\tau_0$ is the closed form printed in the proof of Proposition 6 and $\tau_{FB}=\delta_I/\delta_U-1$. The tax $\tau_0$ is the unique tax at which the two Pareto-optimal equilibria give the same welfare.
--
--   **Formalization Note.** The paper's further remark that $\Delta W$ is decreasing "at a decreasing rate" (the second-derivative display) is not formalized; it is not used for the conclusion.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), proof of Proposition 6 (Appendix A), p. 47, "Hence, τ0 is unique and the separating equilibrium yields greater welfare than the pooling equilibrium if and only if τ < τ0"

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem tau0_step (P : Firm) (VH VL v : ℝ) (hS : Standing P) (h23 : Spec23 P VH VL v)
    (hv : 0 < v) :
    (∀ τ ∈ Set.Icc 0 (tauFB P), (poolWelfare P τ 1 < WS P τ ↔ τ < tau0 P v)) ∧
    (0 ≤ tau0 P v → tau0 P v ≤ tauFB P → WS P (tau0 P v) = poolWelfare P (tau0 P v) 1) := by sorry

end TiltingFTT.Optimal
