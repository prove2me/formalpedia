-- Prove2me | Theorems.Thm_RankingCertGap_gStar_ratio
-- name    : RankingCertGap.gStar_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:28.868663+00:00
-- url     : https://prove2.me/theorems/147f9e46-09d7-4b42-85f6-7a6c344ccf03
-- title:
--   §10.3 and App. J.3, pp.37, 78 — the tight cycle $G^\star$
-- statement:
--   The instance $G^\star$ is two-regular, $\mathrm{OPT}(G^\star)=8$, and
--
--   $$
--   \frac{\mathbb E[\mathrm{RANKING}(G^\star)]}{\mathrm{OPT}(G^\star)}=\frac{119}{144}.
--   $$
--
--   Consequently $\tilde\gamma(2)\le119/144$. Together with (113), this gives $\tilde\gamma(2)=119/144$.
--
--   Differences from the source:
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), §10.3, p.37; App. J.3, p.78

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_TightInstances

namespace RankingCertGap

/-- **The tight cycle.** Xu, arXiv:2610.17545 (held file sha256 75896dd9…), §10.3, p.37 and App. J.3,
p.78: `G★ ∈ B₂`, `OPT(G★) = 8`, `E[RANKING(G★)]/OPT(G★) = 119/144`, and consequently
`γ̃(2) ≤ 119/144`. -/
theorem gStar_ratio :
    gStar.IsRegular 2 ∧ gStar.OPT = 8 ∧
    gStar.rankingValue / (gStar.OPT : ℝ) = 119 / 144 ∧
    gammaC (regular 2) ≤ 119 / 144 := by sorry

end RankingCertGap
