-- Prove2me | Theorems.Thm_VolunteerNotify_display_17
-- name    : VolunteerNotify.display_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:53.566541+00:00
-- url     : https://prove2.me/theorems/077b84e1-02a1-4bc9-a306-b0315c75b2a9
-- title:
--   Display (17), p.20 — weak duality: $\bar J_{v,1}\ge\frac1{2-q}\sum_{t,s}\lambda_{s,t}\bar r_{v,s,t}x_{v,s,t}$
-- statement:
--   Let $x\in\mathcal P$, let $v$ be a volunteer and $q$ the MDHR of $g$. Let $\bar r_{v,s,t}$ be any reals, and let $\bar J_{v,1},\dots,\bar J_{v,T+1}$ be reals with $\bar J_{v,T+1}=0$ that satisfy, for all $t$, the first two constraint sets of (J-LP):
--   $$
--   \bar J_{v,t}\ge\bar J_{v,t+1},\qquad
--   \bar J_{v,t}\ge\bar J_{v,t+1}+\sum_s\lambda_{s,t}x_{v,s,t}\Bigl[\bar r_{v,s,t}-\bar J_{v,t+1}+\sum_{\tau=t+1}^T g(\tau-t)\bar J_{v,\tau}\Bigr].
--   $$
--   Then
--   $$
--   \bar J_{v,1}\ge\frac1{2-q}\sum_{t=1}^T\sum_{s}\lambda_{s,t}\bar r_{v,s,t}x_{v,s,t}. \tag{17}
--   $$
--   This bound holds for the worst-case per-stage rewards, which is what allows the rewards $r$ of (6) to be plugged in.
--
--   Differences from the source:
--   - reading: Table 1 lists variables J̄_{v,t} for t ∈ [T] and uses J̄_{v,T+1} → `Jbar` on T + 1 slots with `Jbar (Fin.last T) = 0`; reason: J_{v,T+1} = 0 on p.16 is the terminal value of the recursion that (J-LP) relaxes
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist, e.g. hazards 1/2 + 1/(τ+2); the infimum equals the minimum whenever it exists, so the statement specializes to the source
--   - encoding: sums over s = 0, …, S → sums over `Fin S`; reason: variables of type 0 are 0 (fn. 18, p.16), so the s = 0 terms vanish
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - generalization: the page argues with x* of (5) → any x ∈ P; reason: only x* ∈ P is used, through dual feasibility; x* ∈ P, so the statement specializes to the source
--   - encoding: (17) bounds the minimum of (J-LP), whose third constraint defines c, for a fixed v → the bound at every point satisfying the first two constraint sets, with c written out as its sum and v dropped from `rbar`, `Jbar`; reason: a lower bound on a minimum is a lower bound at every feasible point; c is defined by that constraint
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, (17), p.20; (J-LP), Table 1, p.19

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_IsDP

namespace VolunteerNotify

/-- Display (17), Manshadi–Rodilitz, arXiv:2002.08474v7, p.20: for `x ∈ P`, any rewards `r̄` and
any `J̄_1, …, J̄_{T+1}` with `J̄_{T+1} = 0` satisfying the first two constraint sets of (J-LP),
Table 1, p.19, `J̄_1 ≥ (1/(2 − q)) ∑_t ∑_s λ_{s,t} r̄_{s,t} x_{v,s,t}`.

**Formalization Note.** `r̄` has no sign constraint. `J̄_{T+1} = 0` is the terminal value of p.16;
Table 1's variables are `t ∈ [T]`. The `s = 0` terms vanish because `x_{v,0,t} = 0` (fn. 18). -/
theorem display_17 {V S T : ℕ} (I : Instance V S T) (x : Decision V S T)
    (hx : x ∈ feasibleSet I) (v : Fin V) (rbar : Fin S → Fin T → ℝ) (Jbar : Fin (T + 1) → ℝ)
    (hlast : Jbar (Fin.last T) = 0)
    (hα : ∀ t : Fin T, Jbar t.succ ≤ Jbar t.castSucc)
    (hγ : ∀ t : Fin T, Jbar t.succ +
      ∑ s, I.lam s t * x v s t * (rbar s t - Jbar t.succ + futureValue I Jbar t) ≤
        Jbar t.castSucc) :
    1 / (2 - mdhr I.g) * ∑ t, ∑ s, I.lam s t * rbar s t * x v s t ≤ Jbar 0 := by sorry

end VolunteerNotify
