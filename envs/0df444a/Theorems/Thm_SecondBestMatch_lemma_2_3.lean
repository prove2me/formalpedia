-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_2_3
-- name    : SecondBestMatch.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:18.563455+00:00
-- url     : https://prove2.me/theorems/c743082b-8245-4909-83d4-2bc6255eb38c
-- title:
--   Lemma 2.3 — ex-ante weak balance can be made exact at every profile
-- statement:
--   Let $\mathcal I$ be an instance with independent priors on $[0,1]$. An allocation rule $q$ admits transfers $p,r$ for which $(q,p,r)$ is BIC, interim IR and ex-ante weakly budget balanced if and only if it admits transfers $p',r'$ for which $(q,p',r')$ is BIC, interim IR and exactly strongly budget balanced at every report profile:
--   $$
--   \exists\,p,r:\ (q,p,r)\ \text{BIC, IIR},\ \textstyle\sum_i\mathbb E[p_i]\ge\sum_j\mathbb E[r_j]
--   \iff
--   \exists\,p',r':\ (q,p',r')\ \text{BIC, IIR},\ \textstyle\sum_i p'_i(\boldsymbol t) = \sum_j r'_j(\boldsymbol t)\ \forall\boldsymbol t\in[0,1]^K .
--   $$
--   BIC and interim IR are on the full report domain and transfers are signed.
--
--   The lemma lets the second best be computed over allocation rules with ex-ante weak budget balance only.
--
--   Differences from the source:
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
--   - encoding: interim expectations $\mathbb E_{\boldsymbol t_{-k}}$ over the other agents' types → integrals over the full product prior with agent $k$'s coordinate overwritten; reason: independence and a unit-mass marginal make the two equal
--   - encoding: finitely many buyers and sellers → finite types `B`, `S` (`Fintype`); reason: Lean convention; same instances
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 2.3, p.9 (proof in Appendix B, pp.31–33)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsAdmissible
import Definitions.Def_SecondBestMatch_IsBIC
import Definitions.Def_SecondBestMatch_IsInterimIR
import Definitions.Def_SecondBestMatch_IsExAnteWBB
import Definitions.Def_SecondBestMatch_IsStrongBB

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 2.3** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.2, p.9). An allocation rule `q` admits transfers `p, r` for which
`(q, p, r)` is BIC, interim IR, and ex-ante weakly budget balanced if and only if it admits
transfers `p', r'` for which `(q, p', r')` is BIC, interim IR, and exactly strongly budget balanced
at every report profile.

**Formalization Note** "Allocation rule" and the finiteness of transfer expectations (p.8) are the
fields of `IsAdmissible`, required on both sides. BIC and interim IR are on the full report domain
`[0, 1]`; transfers are signed. -/
theorem lemma_2_3 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m)
    (q : Profile B S → Finset (B × S) → ℝ) :
    (∃ (p : Profile B S → B → ℝ) (r : Profile B S → S → ℝ),
      IsAdmissible m ⟨q, p, r⟩ ∧ IsBIC m ⟨q, p, r⟩ ∧ IsInterimIR m ⟨q, p, r⟩ ∧
        IsExAnteWBB m ⟨q, p, r⟩) ↔
    (∃ (p' : Profile B S → B → ℝ) (r' : Profile B S → S → ℝ),
      IsAdmissible m ⟨q, p', r'⟩ ∧ IsBIC m ⟨q, p', r'⟩ ∧ IsInterimIR m ⟨q, p', r'⟩ ∧
        IsStrongBB (⟨q, p', r'⟩ : Mechanism B S)) := by sorry

end SecondBestMatch
