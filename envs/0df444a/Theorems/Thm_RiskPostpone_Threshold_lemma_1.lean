-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_lemma_1
-- name    : RiskPostpone.Threshold.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:30.791826+00:00
-- url     : https://prove2.me/theorems/c26060a4-7830-4ffd-93ec-6d3de80a154e
-- title:
--   Lemma 1 — the second-stage optimal price is p(min{q_rξ, d*}) with revenue min{q_rξ, d*}·p(min{q_rξ, d*})
-- statement:
--   In the random-yield model with its standing assumptions, assume Assumption 2 and let $d^*\in[0,d(0)]$ maximize the revenue $x\mapsto p(x)\,x$ over $[0,d(0)]$. For on-hand inventory $q_r\xi$ with $q_r\ge0$, $\xi\ge0$, put $m=\min\{q_r\xi,d^*\}$. Then the price $p_r^*=p(m)$ lies in $[0,p_0]$, earns revenue $p(m)\min\{d(p(m)),q_r\xi\}=m\,p(m)$, and this is the optimal second-stage revenue:
--   $$
--   \max_{p_r\in[0,p_0]}p_r\min\{d(p_r),q_r\xi\}=\min\{q_r\xi,d^*\}\;p\big(\min\{q_r\xi,d^*\}\big).
--   $$
--
--   With ample supply the firm sells exactly the unconstrained revenue-maximizing demand $d^*$; with scarce supply it clears its inventory.
--
--   **Formalization Note** The paper defines $d^*$ by the first-order condition $p'(d^*)d^*+p(d^*)=0$; here $d^*$ is any maximizer of the revenue on $[0,d(0)]$, which coincides with the first-order root when the revenue is differentiable and concave. Twice differentiability in Assumption 2 is not needed.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. 13, Lemma 1

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_Setting

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Lemma 1 (p. 13): under Assumption 2, with `d*` a maximizer of the revenue `x ↦ P(x)·x` on
`[0, d(0)]` and on-hand inventory `q·ξ ≥ 0`, the price `P(min{qξ, d*})` lies in `[0, p0]`,
earns `min{qξ, d*}·P(min{qξ, d*})`, and this is the maximal second-stage revenue
`max_{p ∈ [0,p0]} p·min{d(p), qξ}`. -/
theorem lemma_1 (M : Model) (hM : M.Standing) (hA2 : M.Assumption2) (dstar : ℝ)
    (hds : dstar ∈ Icc 0 (M.d 0)) (hmax : IsMaxOn (fun x => M.P x * x) (Icc 0 (M.d 0)) dstar)
    (q ξ : ℝ) (hq : 0 ≤ q) (hξ : 0 ≤ ξ) :
    M.P (min (q * ξ) dstar) ∈ Icc 0 M.p0 ∧
    M.P (min (q * ξ) dstar) * min (M.d (M.P (min (q * ξ) dstar))) (q * ξ) =
      min (q * ξ) dstar * M.P (min (q * ξ) dstar) ∧
    IsGreatest ((fun p => p * min (M.d p) (q * ξ)) '' Icc 0 M.p0)
      (min (q * ξ) dstar * M.P (min (q * ξ) dstar)) := by sorry

end RiskPostpone.Threshold
