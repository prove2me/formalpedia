-- Prove2me | Theorems.Thm_PlatformQualReg_ExclSubsid_exclusion_special_case
-- name    : PlatformQualReg.ExclSubsid.exclusion_special_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:59.698771+00:00
-- url     : https://prove2.me/theorems/6cfa2474-70fb-45d0-a8ef-2f35c63e0b7c
-- title:
--   Proposition 4 discussion, p. 26: exclusion outcome replicated by a subsidy
-- statement:
--   Let an exclusion outcome be feasible. If
--
--   $$
--   \gamma=\frac{\theta_dn}{\lambda}-(\alpha_{dh}-\alpha_{dl})m\ge0,
--   $$
--
--   set the subsidy outcome's developer fee to $p_d^S=\alpha_{dl}m-bn$, retain the exclusion consumer fee and network sizes, and pay this $\gamma$ to high-quality developers. The resulting subsidy outcome is feasible, has $n_l=0$ and $n_h=n$, and has exactly the exclusion profit.
--
--   This construction formalizes the replication argument immediately after Proposition 4: a higher posted developer fee excludes low-quality developers, while the subsidy offsets it for high-quality developers.
--
--   **Formalization Note** Nonnegativity of the displayed subsidy is a necessary condition for this particular construction under the paper's $\gamma\ge0$ rule. The milestone states it explicitly for a feasible exclusion outcome; the goal concerns optimal outcomes.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, p. 26 (PDF 27), paragraph immediately after Proposition 4

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid

/-- The replication claim following Proposition 4, printed p. 26 (PDF 27). -/
theorem exclusion_special_case (P : Params) (hP : P.Standing)
    (x : OutcomeE) (hx : FeasibleE P x)
    (hγ : 0 ≤ P.thd * x.n / P.lam - (P.adh - P.adl) * x.m) :
    let y : OutcomeS :=
      ⟨P.adl * x.m - P.b * x.n, x.pc,
        P.thd * x.n / P.lam - (P.adh - P.adl) * x.m, x.m, x.n⟩
    FeasibleS P y ∧ nl P y = 0 ∧ nh P y = x.n ∧
    profitS P y = profitE P x := by sorry

end PlatformQualReg.ExclSubsid
