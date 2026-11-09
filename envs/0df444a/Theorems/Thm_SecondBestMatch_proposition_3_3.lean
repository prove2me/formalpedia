-- Prove2me | Theorems.Thm_SecondBestMatch_proposition_3_3
-- name    : SecondBestMatch.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:16.243192+00:00
-- url     : https://prove2.me/theorems/4451d2d4-d9a1-46d3-8a2a-ec84d17cdc26
-- title:
--   Proposition 3.3 — the second-best program and its Lagrangian dual
-- statement:
--   For finite-support priors,
--   $$
--   \mathrm{SB} = \max_{q\in\mathcal P:\ \mathcal B(q)\ge0}\mathcal G(q),
--   \qquad
--   \mathrm{SB} = \inf_{\alpha\ge0}\ \max_{q\in\mathcal P}\big(\mathcal G(q)+\alpha\,\mathcal B(q)\big). \tag{1}
--   $$
--   The statement has three parts: (i) some $q\in\mathcal P$ with $\mathcal B(q)\ge0$ has $\mathcal G(q) = \mathrm{SB}$, and no such $q$ exceeds $\mathrm{SB}$; (ii) for every $\alpha\ge0$ the inner maximum is attained and equals $\mathcal L(\alpha)$; (iii) Eq. (1).
--
--   Differences from the source:
--   - encoding: max over $\mathcal P$ → a maximizer in $\mathcal P$ (attained and no larger value), and $\mathcal L(\alpha)$ as a real supremum equal to it; reason: states the maximum without relying on a junk-free `sSup`
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Proposition 3.3, p.11, Eq. (1)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_InPolytope
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_virtGFT
import Definitions.Def_SecondBestMatch_secondBest
import Definitions.Def_SecondBestMatch_lagrangianValue

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Proposition 3.3** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2, p.11, Eq. (1)). For finite-support priors,
`SB = max_{q ∈ 𝒫 : ℬ(q) ≥ 0} 𝒢(q)`. Moreover, `SB = inf_{α ≥ 0} max_{q ∈ 𝒫} (𝒢(q) + α ℬ(q))`.

Clause (i) is the primal maximum, attained; clause (ii) says that the inner maximum of (1) is
attained, for every `α ≥ 0`, and equals `ℒ(α)`; clause (iii) is Eq. (1). -/
theorem proposition_3_3 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S) (hm : IsUnitMarket m)
    (hfs : IsFiniteSupportMarket m) :
    ((∃ q, InPolytope m q ∧ 0 ≤ virtGFT m q ∧ ordGFT m q = secondBest m) ∧
      ∀ q, InPolytope m q → 0 ≤ virtGFT m q → ordGFT m q ≤ secondBest m) ∧
    (∀ α : ℝ, 0 ≤ α → ∃ q, InPolytope m q ∧
      (∀ q', InPolytope m q' → ordGFT m q' + α * virtGFT m q' ≤ ordGFT m q + α * virtGFT m q) ∧
      ordGFT m q + α * virtGFT m q = lagrangianValue m α) ∧
    secondBest m = sInf (lagrangianValue m '' Ici 0) := by sorry

end SecondBestMatch
