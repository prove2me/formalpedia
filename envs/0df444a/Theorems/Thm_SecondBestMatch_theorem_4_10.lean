-- Prove2me | Theorems.Thm_SecondBestMatch_theorem_4_10
-- name    : SecondBestMatch.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:56.485386+00:00
-- url     : https://prove2.me/theorems/c00be2e9-b048-4fe3-b5a7-aa26d1e3276f
-- title:
--   Theorem 4.10 — half efficiency for finite-support priors
-- statement:
--   If all priors have finite support, then
--   $$
--   \mathrm{SB}\ \ge\ \tfrac12\,\mathrm{FB}.
--   $$
--
--   Differences from the source:
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
--   - encoding: interim expectations $\mathbb E_{\boldsymbol t_{-k}}$ over the other agents' types → integrals over the full product prior with agent $k$'s coordinate overwritten; reason: independence and a unit-mass marginal make the two equal
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Theorem 4.10, p.18

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_firstBestGFT
import Definitions.Def_SecondBestMatch_secondBest

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Theorem 4.10** (half efficiency; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.3, p.18). If all priors have finite support, then
`SB ≥ ½ FB`. -/
theorem theorem_4_10 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m)
    (hfs : IsFiniteSupportMarket m) :
    1 / 2 * firstBestGFT m ≤ secondBest m := by sorry

end SecondBestMatch
