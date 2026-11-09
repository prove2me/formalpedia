-- Prove2me | Theorems.Thm_ProxGapTight_thresholds_ordered
-- name    : ProxGapTight.thresholds_ordered
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:48:40.11302+00:00
-- url     : https://prove2.me/theorems/34942d08-bd85-46af-94cd-61a4a8f715b1
-- title:
--   §1.1, p.2 — $J_{3/2}(\delta)<\Gamma(\delta)<\delta$
-- statement:
--   For every $0<\delta<1$,
--   $$
--   J_{3/2}(\delta)<\Gamma(\delta)<\delta,
--   $$
--   where $J_{3/2}(\delta)=1-(1-\delta)^{1/3}$ and $\Gamma(\delta)=1-(1-\delta)^{4/9}$.
--
--   The first inequality makes the range of radii $\rho\in(J_{3/2}(\delta),\Gamma(\delta))$ of the main theorem nonempty; the second makes $\eta_0=\min\{\eta,(\delta-\Gamma(\delta))/4\}$ positive in its proof.
--
--   Differences from the source: none.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §1.1, p.2, display

import Mathlib
import Definitions.Def_ProxGapTight_J32
import Definitions.Def_ProxGapTight_Gam

namespace ProxGapTight

/-- **The thresholds are ordered**, Kominers, Thaler, Zheng, manuscript (Sept. 2026), §1.1, p.2,
display: "Note that for every 0 < δ < 1, J_{3/2}(δ) < Γ(δ) < δ." Both inequalities. -/
theorem thresholds_ordered (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    J32 δ < Gam δ ∧ Gam δ < δ := by sorry

end ProxGapTight
