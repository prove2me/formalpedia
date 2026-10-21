-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_proposition_1
-- name    : ValueTrial.Asymptotic.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:21.160626+00:00
-- url     : https://prove2.me/theorems/11c7f636-bc9b-4a23-9230-0cda54ef9d03
-- title:
--   Proposition 1, p. 13 (PDF 15) — an optimal trial design (T*, r*) exists
-- statement:
--   Consider the value-based trial model under its standing assumptions, with $T_{\max}>0$ and $0\le r_{\max}\le\zeta$. Suppose that the setup cost $c_{cap}$ is non-decreasing, lower semicontinuous and nonnegative on $[0,r_{\max}]$, and that the post-adoption population $P(T)$ is non-increasing, bounded, upper semicontinuous and nonnegative on $[0,T_{\max}]$. Then problem (5),
--   $$
--   V^*=\max_{T,r}V(T,r)\quad\text{s.t. }T\in[0,T_{\max}],\ r\in[0,r_{\max}],
--   $$
--   has an optimal solution $(T^*,r^*)$.
--
--   Existence is not automatic: $V$ jumps where the trial stops running ($T=0$ or $r=0$), and the assumptions are what make it upper semicontinuous there.
--
--   **Formalization Note** Nonnegativity of $c_{cap}$ is added: the proof uses "because $c_{cap}(r)\ge0$" (p. ec4), and with a negative setup cost the supremum is approached as $Tr\downarrow0$ but not attained. Nonnegativity of $P(T)$ is the model's standing condition (Table EC.1). The hypotheses on $c_{cap}$ and $P$ are imposed on the decision ranges $[0,r_{\max}]$ and $[0,T_{\max}]$, where the page uses them. The discount rate $\rho\in[0,1)$ is arbitrary.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. 13 (PDF 15), Proposition 1; proof App. C.1, pp. ec3–ec4 (PDF 40–41)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Proposition 1, p. 13 (PDF 15): if the setup cost `ccap` is non-decreasing and lower
semicontinuous on `[0, rmax]` (and nonnegative), and the post-adoption population `P(T)` is
non-increasing, bounded and upper semicontinuous on `[0, Tmax]` (and nonnegative), then
problem (5) has an optimal solution `(T*, r*)`. Table EC.1 gives `Tmax > 0` and
`0 ≤ rmax ≤ ζ`. -/
theorem proposition_1 (θ : Params) (hS : θ.Standing) (Tmax rmax : ℝ)
    (hTmax : 0 < Tmax) (hrmax : 0 ≤ rmax) (hrcap : rmax ≤ θ.zeta) (ccap Ppop : ℝ → ℝ)
    (hcm : MonotoneOn ccap (Set.Icc 0 rmax))
    (hcl : LowerSemicontinuousOn ccap (Set.Icc 0 rmax))
    (hc0 : ∀ r ∈ Set.Icc 0 rmax, 0 ≤ ccap r)
    (hPa : AntitoneOn Ppop (Set.Icc 0 Tmax))
    (hPb : BddAbove (Ppop '' Set.Icc 0 Tmax))
    (hPu : UpperSemicontinuousOn Ppop (Set.Icc 0 Tmax))
    (hP0 : ∀ T ∈ Set.Icc 0 Tmax, 0 ≤ Ppop T) :
    ∃ x : ℝ × ℝ, IsOptOn (V θ ccap Ppop) (box Tmax rmax) x := by sorry

end ValueTrial.Asymptotic
