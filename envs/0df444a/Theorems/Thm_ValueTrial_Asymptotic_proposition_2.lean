-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_proposition_2
-- name    : ValueTrial.Asymptotic.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:24.538261+00:00
-- url     : https://prove2.me/theorems/d369b9f0-b0c9-4408-a7f4-c8ae3427e74c
-- title:
--   Proposition 2, p. 14 (PDF 16) — Case I: only the sample size Tr/2 matters
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting ($\rho=0$), with a constant setup cost $c_{cap}(r)=k\ge0$ and a fixed patient pool $P(T)=P>0$, and bounds $T_{\max}>0$, $0\le r_{\max}\le\zeta$. Then there is a number of pairs $Q^*$, attained by some feasible design, such that every design in
--   $$
--   S=\{(T,r)\in[0,T_{\max}]\times[0,r_{\max}] : Tr/2=Q^*\}
--   $$
--   solves problem (5).
--
--   In Case I of the paper's taxonomy the problem thus reduces to choosing the sample size; the split between duration and rate is free.
--
--   **Formalization Note** The statement asserts that some $Q^*$ is attained by a feasible design and that all designs with that sample size are optimal, so $Q^*$ is an optimal sample size. The setup cost is required nonnegative (the model's convention, used in Proposition 1, on which the existence of an optimum rests).
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. 14 (PDF 16), Proposition 2; proof App. C.2, p. ec4 (PDF 41)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Proposition 2, p. 14 (PDF 16): with a constant setup cost `ccap`, no discounting and a fixed
patient pool `P`, there is an optimal number of pairs `Q*` such that every
`(T, r) ∈ [0, Tmax] × [0, rmax]` with `Tr/2 = Q*` solves (5), with the finite
bounds and `P > 0` of Table EC.1. -/
theorem proposition_2 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (Tmax rmax : ℝ)
    (hTmax : 0 < Tmax) (hrmax : 0 ≤ rmax) (hrcap : rmax ≤ θ.zeta)
    (k : ℝ) (hk : 0 ≤ k) (P : ℝ) (hP : 0 < P) :
    ∃ Qs : ℝ, (∃ x ∈ box Tmax rmax, x.1 * x.2 / 2 = Qs) ∧
      ∀ x ∈ box Tmax rmax, x.1 * x.2 / 2 = Qs →
        IsOptOn (V θ (fun _ => k) (fixedPool P)) (box Tmax rmax) x := by sorry

end ValueTrial.Asymptotic
