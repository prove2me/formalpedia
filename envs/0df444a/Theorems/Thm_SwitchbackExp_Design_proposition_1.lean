-- Prove2me | Theorems.Thm_SwitchbackExp_Design_proposition_1
-- name    : SwitchbackExp.Design.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:58.883035+00:00
-- url     : https://prove2.me/theorems/ff17ea2d-24b2-41b4-b7ed-9100a9a6fa92
-- title:
--   Proposition 1, p. 10 — under Assumptions 1–2 the Horvitz–Thompson estimator is unbiased for τ_m in every regular switchback experiment
-- statement:
--   Let $(\mathbb T,\mathbb Q)$ be a regular switchback design on $[T]$, with $m<T$, randomization points $\mathbb T=\{t_0=1<\dots<t_K\}$, $K\ge1$, and probabilities $q_{t_k}\in(0,1)$. Let $\mathbb Y$ be potential outcomes satisfying Assumption 1 (non-anticipation) and Assumption 2 ($m$-carryover). Then the Horvitz–Thompson estimator $\hat\tau_m$ of (4) is unbiased for the lag-$m$ effect $\tau_m(\mathbb Y)$ of (1):
--   $$\mathbb E_{W_{1:T}\sim\eta_{\mathbb T,\mathbb Q}}\bigl[\hat\tau_m(\eta_{\mathbb T,\mathbb Q},W_{1:T},\mathbb Y)\bigr]=\tau_m(\mathbb Y).$$
--
--   Unbiasedness makes the risk (5) the variance of the estimator, which is what the design problem of §3 minimizes.
--
--   **Formalization Note** The page states the result for a general lag $p$; the mission works with $p=m$, the standing choice of §2.2 and §3. Assumption 3 is not needed and not assumed.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Proposition 1, p. 10; proof EC.2, p. ec2

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Proposition 1 (p. 10): in a regular switchback experiment, under Assumptions 1 and 2, the
Horvitz–Thompson estimator (4) is unbiased for the lag-`m` estimand (1). -/
theorem proposition_1 (m T : ℕ) (hmT : m < T) (P : Finset ℕ) (q : ℕ → ℝ)
    (hP : IsRegularPoints T P) (hq : IsRegularProbs P q) (Y : Outcomes)
    (hY1 : NonAnticipating T Y) (hY2 : Carryover m T Y) :
    expect P q (htEstimator m T P q Y) = tau m T Y := by sorry

end SwitchbackExp.Design
