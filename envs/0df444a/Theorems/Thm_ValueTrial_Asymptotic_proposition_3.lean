-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_proposition_3
-- name    : ValueTrial.Asymptotic.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:15.114261+00:00
-- url     : https://prove2.me/theorems/e48268cb-2bd5-456a-b9d1-f3bf6fb01982
-- title:
--   Proposition 3, p. 14 (PDF 16) — constant setup cost: an optimum recruits at the maximal rate
-- statement:
--   Consider the value-based trial model under its standing assumptions, with any discount rate $\rho\in[0,1)$, bounds $T_{\max}>0$, $0\le r_{\max}\le\zeta$, a constant setup cost $c_{cap}(r)=k\ge0$, and a post-adoption population $P(T)$ that is non-increasing, bounded, upper semicontinuous and nonnegative on $[0,T_{\max}]$. Then problem (5) has an optimal solution $(T^*,r^*)$ with $r^*=r_{\max}$; equivalently
--   $$
--   V^*=\max_{T\in[0,T_{\max}]}V(T,r_{\max}). \tag{10}
--   $$
--
--   With constant setup costs, recruiting faster lets the adoption decision come earlier at no extra capacity cost, so Case II reduces to a one-dimensional problem in $T$.
--
--   **Formalization Note** The hypotheses on $P(\cdot)$ are those of Proposition 1, which §3.3 makes standing for the section (the proposition asserts that an optimal solution exists); the setup cost is required nonnegative, as in Proposition 1.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. 14 (PDF 16), Proposition 3, eq. (10); proof App. C.2, pp. ec4–ec6 (PDF 41–43)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Proposition 3, p. 14 (PDF 16): with a constant setup cost `ccap` (and `P(T)` as in
Proposition 1), problem (5) has an optimal solution with `r* = rmax`, so that
`V* = max_{T ∈ [0, Tmax]} V(T, rmax)` (10), with the finite bounds of Table EC.1. -/
theorem proposition_3 (θ : Params) (hS : θ.Standing) (Tmax rmax : ℝ)
    (hTmax : 0 < Tmax) (hrmax : 0 ≤ rmax) (hrcap : rmax ≤ θ.zeta)
    (k : ℝ) (hk : 0 ≤ k) (Ppop : ℝ → ℝ)
    (hPa : AntitoneOn Ppop (Set.Icc 0 Tmax))
    (hPb : BddAbove (Ppop '' Set.Icc 0 Tmax))
    (hPu : UpperSemicontinuousOn Ppop (Set.Icc 0 Tmax))
    (hP0 : ∀ T ∈ Set.Icc 0 Tmax, 0 ≤ Ppop T) :
    ∃ T : ℝ, IsOptOn (V θ (fun _ => k) Ppop) (box Tmax rmax) (T, rmax) := by sorry

end ValueTrial.Asymptotic
