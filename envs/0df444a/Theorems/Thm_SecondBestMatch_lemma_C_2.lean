-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_C_2
-- name    : SecondBestMatch.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:27:27.984092+00:00
-- url     : https://prove2.me/theorems/2d9105b4-4a6f-468f-94f8-159d3840584a
-- title:
--   Lemma C.2 — lifting a rounded mechanism
-- statement:
--   Let $\mathcal I$ be an instance with priors on $[0,1]$, $n\ge1$, and let $(q^n,p^n,r^n)$ be a full-domain BIC and interim-IR mechanism for the rounded instance $\mathcal I_n$ whose transfers balance exactly at every report profile. Then $\mathcal I$ admits a full-domain BIC and interim-IR mechanism with exact profile-wise strong budget balance and
--   $$
--   \mathrm{GFT}_{\mathcal I}(\tilde q)\ \ge\ \mathrm{GFT}_{\mathcal I_n}(q^n).
--   $$
--
--   Differences from the source:
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
--   - encoding: interim expectations $\mathbb E_{\boldsymbol t_{-k}}$ over the other agents' types → integrals over the full product prior with agent $k$'s coordinate overwritten; reason: independence and a unit-mass marginal make the two equal
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma C.2, p.34

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsSBFeasible
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_roundedMarket

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma C.2** (lifting a rounded mechanism; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), App. C, p.34). Let `(qⁿ, pⁿ, rⁿ)` be a
full-domain BIC and interim-IR mechanism for `ℐ_n` whose transfers balance exactly at every report
profile. Then `ℐ` admits a full-domain BIC and interim-IR mechanism with exact profile-wise strong
budget balance and GFT at least the GFT of `qⁿ` in `ℐ_n`. -/
theorem lemma_C_2 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m) (n : ℕ) (hn : 1 ≤ n)
    (A : Mechanism B S) (hA : IsSBFeasible (roundedMarket m n) A) :
    ∃ A' : Mechanism B S, IsSBFeasible m A' ∧
      ordGFT (roundedMarket m n) A.alloc ≤ ordGFT m A'.alloc := by sorry

end SecondBestMatch
