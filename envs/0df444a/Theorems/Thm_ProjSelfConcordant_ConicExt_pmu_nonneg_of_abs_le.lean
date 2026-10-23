-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_nonneg_of_abs_le
-- name    : ProjSelfConcordant.ConicExt.pmu_nonneg_of_abs_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:04.512642+00:00
-- url     : https://prove2.me/theorems/6ebfe4f3-48a8-4508-9c4b-d37ad29aec53
-- title:
--   §2, p. 5 — if |μ| ≤ 2γ then p_μ(t) ≥ 0 for all t (concavity in μ)
-- statement:
--   Let $\nu\ge2$, $\gamma=(\nu-2)/\sqrt{\nu-1}$, and let $\mu$ satisfy $\mu\in[\mu_-,\mu_+]=[-2\gamma,2\gamma]$. Then
--   $$p_\mu(t)=4(\nu-1)t^6+12(\nu-2)t^4+4\mu t^3+12(\nu-3)t^2+12\mu t+4\nu-\mu^2\ge0\qquad\forall t\in\mathbb R.$$
--
--   Together with the necessity statement this shows that $2\gamma$ is exactly the range of $|\mu|$ for which the sextic is nonnegative, which is where the constant $\gamma=(\nu-2)/\sqrt{\nu-1}$ of Theorem 1.5 comes from.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 ('Since p_µ(t) is concave in µ …')

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: if `ν ≥ 2` and `μ ∈ [μ−, μ+]`, i.e. `|μ| ≤ 2γ` with `γ = (ν − 2)/√(ν − 1)`,
then `p_μ(t) ≥ 0` for every real `t`. -/
theorem pmu_nonneg_of_abs_le (ν μ : ℝ) (hν : 2 ≤ ν)
    (hμ : |μ| ≤ 2 * ((ν - 2) / Real.sqrt (ν - 1))) :
    ∀ t : ℝ, 0 ≤ pmu ν μ t := by sorry

end ProjSelfConcordant.ConicExt
