-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_zero_multiplier_gittins_limit
-- name    : PandoraBO.Private20261023.zero_multiplier_gittins_limit
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:20.056733+00:00
-- url     : https://prove2.me/theorems/98e002d5-12f6-4a77-af42-19ff86cb74fe
-- title:
--   New boundary lemma — Gittins policies as the multiplier decreases to zero
-- statement:
--   For any positive nonincreasing sequence $\lambda_k\to0$, there exist positive-multiplier Gittins policies $\pi_k$ and a zero-multiplier Gittins policy $\pi_0$, with indices $g_i(0)=\operatorname{ess\,sup}F_i$ in the extended reals, such that
--
--   $$R(\pi_0)=R_{\mathrm{all}},\qquad C(\pi_k)\to C(\pi_0),\qquad R(\pi_k)\to R(\pi_0).$$
--
--   The same policy sequence satisfies both limits along the full natural-number sequence. The conclusion is existential and permits choosing ties; it does not say arbitrary zero-index tie rules have minimal cost, or satisfy any prescribed budget. No budget or strict reward-gap hypothesis appears.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin, Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, NeurIPS 2024; arXiv:2406.20062v3 (16 January 2025), https://arxiv.org/pdf/2406.20062v3. Proposed new boundary lemma for the corrected Theorem 2; not stated in arXiv v3. Extends the policy-limit argument to essential-supremum indices at zero. Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem zero_multiplier_gittins_limit {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (hpos : ∀ k, 0 < multipliers k)
    (hmono : Antitone multipliers)
    (hlim : Filter.Tendsto multipliers Filter.atTop (nhds 0)) :
    ∃ policies : ℕ → Policy n, ∃ π : Policy n,
      (∀ k, isGittinsPolicy M (multipliers k) (policies k)) ∧
      isZeroGittinsPolicy M π ∧
      expectedReward M π = fullInformationReward M ∧
      Filter.Tendsto (fun k => expectedCost M (policies k))
        Filter.atTop (nhds (expectedCost M π)) ∧
      Filter.Tendsto (fun k => expectedReward M (policies k))
        Filter.atTop (nhds (expectedReward M π)) := by sorry

end PandoraBO.Private20261023
