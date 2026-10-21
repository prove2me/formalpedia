-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_proposition_4
-- name    : ValueTrial.Asymptotic.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:26.936179+00:00
-- url     : https://prove2.me/theorems/c3bb3f8f-372f-46f0-9f9c-845c240ec6f6
-- title:
--   Proposition 4, p. 14 (PDF 16) — fixed pool, no discounting: an optimum runs for the maximal duration
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting ($\rho=0$), with a fixed patient pool $P(T)=P>0$, bounds $T_{\max}>0$, $0\le r_{\max}\le\zeta$, and a setup cost $c_{cap}$ that is non-decreasing, lower semicontinuous and nonnegative on $[0,r_{\max}]$. Then problem (5) has an optimal solution $(T^*,r^*)$ with $T^*=T_{\max}$; equivalently
--   $$
--   V^*=\max_{r\in[0,r_{\max}]}V(T_{\max},r). \tag{11}
--   $$
--
--   With a fixed pool and no discounting there is no penalty for recruiting later, so Case III reduces to choosing the recruitment rate.
--
--   **Formalization Note** The hypotheses on $c_{cap}$ are those of Proposition 1, standing for §3.3 (the proposition asserts that an optimal solution exists).
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. 14 (PDF 16), Proposition 4, eq. (11); proof App. C.2, p. ec6 (PDF 43)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Proposition 4, p. 14 (PDF 16): with a fixed patient pool `P` and no discounting (and `ccap`
as in Proposition 1), problem (5) has an optimal solution with `T* = Tmax`, so that
`V* = max_{r ∈ [0, rmax]} V(Tmax, r)` (11), with the finite bounds and `P > 0`
of Table EC.1. -/
theorem proposition_4 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (Tmax rmax : ℝ)
    (hTmax : 0 < Tmax) (hrmax : 0 ≤ rmax) (hrcap : rmax ≤ θ.zeta) (ccap : ℝ → ℝ)
    (hcm : MonotoneOn ccap (Set.Icc 0 rmax))
    (hcl : LowerSemicontinuousOn ccap (Set.Icc 0 rmax))
    (hc0 : ∀ r ∈ Set.Icc 0 rmax, 0 ≤ ccap r) (P : ℝ) (hP : 0 < P) :
    ∃ r : ℝ, IsOptOn (V θ ccap (fixedPool P)) (box Tmax rmax) (Tmax, r) := by sorry

end ValueTrial.Asymptotic
