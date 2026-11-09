-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_3_2
-- name    : SecondBestMatch.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:10.474119+00:00
-- url     : https://prove2.me/theorems/b38950d8-4c20-4b98-8345-3619536b7f53
-- title:
--   Lemma 3.2 — budget surplus is at most the virtual GFT, with equality attainable
-- statement:
--   Let the priors have finite support and fix $q\in\mathcal P$.
--
--   1. Every full-domain BIC and interim-IR mechanism that uses $q$ at every support profile satisfies
--   $$
--   \mathbb E_{\boldsymbol t\sim\pi}\Big[\sum_{i\in B}p_i(\boldsymbol t)-\sum_{j\in S}r_j(\boldsymbol t)\Big]\ \le\ \mathcal B(q).
--   $$
--   2. Equality is attainable by such a mechanism.
--   3. Consequently, $q$ admits an ex-ante weakly budget-balanced implementation (full-domain BIC, interim IR, using $q$ at every support profile) if and only if $\mathcal B(q)\ge 0$.
--
--   Differences from the source:
--   - encoding: a mechanism that uses $q$ at every support profile → `A.alloc t M = q t M` for every profile `t` of the support product and every `M`; reason: literal reading
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
--   - encoding: interim expectations $\mathbb E_{\boldsymbol t_{-k}}$ over the other agents' types → integrals over the full product prior with agent $k$'s coordinate overwritten; reason: independence and a unit-mass marginal make the two equal
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 3.2, p.11 (proof in Appendix D, p.37)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_IsSupportProfile
import Definitions.Def_SecondBestMatch_IsAdmissible
import Definitions.Def_SecondBestMatch_IsBIC
import Definitions.Def_SecondBestMatch_IsInterimIR
import Definitions.Def_SecondBestMatch_IsExAnteWBB
import Definitions.Def_SecondBestMatch_InPolytope
import Definitions.Def_SecondBestMatch_virtGFT

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 3.2** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2, p.11). Fix `q ∈ 𝒫`. Every full-domain BIC and interim-IR
mechanism that uses `q` at every support profile satisfies
`E_{t∼π}[Σ_{i ∈ B} pᵢ(t) − Σ_{j ∈ S} rⱼ(t)] ≤ ℬ(q)`. Equality is attainable. Consequently, `q`
admits an ex-ante weakly budget-balanced implementation if and only if `ℬ(q) ≥ 0`.

**Formalization Note** "Uses `q` at every support profile" is `A.alloc t = q t` at every profile
in the support product. A mechanism is admissible (`IsAdmissible`: a Borel kernel into `Δ(ℱ)`
with finite transfer expectations); an implementation is an admissible, full-domain BIC and
interim-IR mechanism using `q`. -/
theorem lemma_3_2 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m) (hfs : IsFiniteSupportMarket m)
    (q : Profile B S → Finset (B × S) → ℝ) (hq : InPolytope m q) :
    (∀ A : Mechanism B S, IsAdmissible m A → IsBIC m A → IsInterimIR m A →
      (∀ t, IsSupportProfile m t → ∀ M, A.alloc t M = q t M) →
        ∫ t, (∑ i, A.pay t i - ∑ j, A.recv t j) ∂typeMeasure m ≤ virtGFT m q) ∧
    (∃ A : Mechanism B S, IsAdmissible m A ∧ IsBIC m A ∧ IsInterimIR m A ∧
      (∀ t, IsSupportProfile m t → ∀ M, A.alloc t M = q t M) ∧
        ∫ t, (∑ i, A.pay t i - ∑ j, A.recv t j) ∂typeMeasure m = virtGFT m q) ∧
    ((∃ A : Mechanism B S, IsAdmissible m A ∧ IsBIC m A ∧ IsInterimIR m A ∧ IsExAnteWBB m A ∧
        (∀ t, IsSupportProfile m t → ∀ M, A.alloc t M = q t M)) ↔ 0 ≤ virtGFT m q) := by sorry

end SecondBestMatch
