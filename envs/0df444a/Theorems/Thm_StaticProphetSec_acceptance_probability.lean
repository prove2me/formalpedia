-- Prove2me | Theorems.Thm_StaticProphetSec_acceptance_probability
-- name    : StaticProphetSec.acceptance_probability
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:01.38689+00:00
-- url     : https://prove2.me/theorems/404ef449-f526-4835-ba4b-f424d7c0ee29
-- title:
--   p.16 — acceptance probability $\mathbb 1(i\text{ eligible})\min(1,k/D)$ and formula (5)
-- statement:
--   Fix values $V$ and coins $B$, with demand $D$. Over a uniformly random arrival order, the policy accepts applicant $i$ with probability
--
--   $$\mathbb 1(i\text{ eligible})\,\min\left(1,\frac kD\right).$$
--
--   Consequently the performance of the sequential policy equals formula (5):
--
--   $$\mathcal{ST}^t_k(F)=\mathbb E\Big[\sum_{i=1}^nV_i\,\mathbb 1(i\text{ eligible})\,\min\left(1,\frac kD\right)\Big].$$
--
--   This links the operational definition of the policy to the formula used in the rest of the proof.
--
--   **Formalization Note** The probability over the arrival order is the fraction of the $n!$ permutations under which $i$ is accepted.
--
--   Differences from the source:
--
--   - generalization: threshold $t$ and $D^t(V)$ → policy $(t,p)$ with tie-breaking coins and $D$ counting eligible applicants; reason: Remark 1, p.5, says all results apply to it; $p=0$ recovers the plain threshold
--   - generalization: values with finite expectations are the implicit reading of ratios → expectations in $[0,\infty]$ with no integrability assumption; reason: the source assumes none; every finite instance is covered
--   - encoding: probability over the arrival order → count of permutations divided by $n!$; reason: the arrival order is uniform on a finite set
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Definition 1 and the paragraph after it, p.16

import Mathlib
import Definitions.Def_StaticProphetSec_accepted
import Definitions.Def_StaticProphetSec_coinProb
import Definitions.Def_StaticProphetSec_performance

open MeasureTheory
open scoped ENNReal Nat

namespace StaticProphetSec

/-- The acceptance probability and formula (5) (Arnosti & Ma, arXiv:2108.12893v2, Definition 1
and the paragraph after it, p.16; with tie-breaking, Remark 1, p.5). Given the values and coins,
over a uniform arrival order, applicant `i` is accepted with probability
`𝟙(i eligible) min(1, k/D)`; consequently the performance of the sequential policy equals formula
(5). -/
theorem acceptance_probability {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0)
    (t p : ℝ) (ht : 0 ≤ t) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ (V : Fin n → ℝ) (B : Fin n → Bool) (i : Fin n),
      (((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => i ∈ accepted k t V B σ).card : ℕ) : ℝ)
          / (n ! : ℝ) =
        if i ∈ eligibleSet t V B then min 1 ((k : ℝ) / (demand t V B : ℝ)) else 0) ∧
    performance k μ t p =
      ∫⁻ V, ∑ B : Fin n → Bool, coinProb p B * ∑ i, ENNReal.ofReal (V i) *
        (if i ∈ eligibleSet t V B then
          ENNReal.ofReal (min 1 ((k : ℝ) / (demand t V B : ℝ))) else 0) ∂Measure.pi μ := by sorry

end StaticProphetSec
