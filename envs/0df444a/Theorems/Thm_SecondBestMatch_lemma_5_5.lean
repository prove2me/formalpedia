-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_5_5
-- name    : SecondBestMatch.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:32.71873+00:00
-- url     : https://prove2.me/theorems/abc5c524-0110-46d3-bb7a-442412a55bb1
-- title:
--   Lemma 5.5 — tightness of the Beta coefficient
-- statement:
--   For every $\alpha\ge0$,
--   $$
--   \inf_{\mathcal I:\ \mathrm{FB}(\mathcal I)>0}\frac{\mathcal L_{\mathcal I}(\alpha)}{\mathrm{FB}(\mathcal I)} = g_\alpha ,
--   $$
--   where the infimum is over all instances with finite-support priors; moreover, the infimum is approached by bilateral instances. The statement has two clauses:
--
--   1. for every instance with finite-support priors and $\mathrm{FB}>0$, some $q\in\mathcal P$ has $\mathcal G(q)+\alpha\,\mathcal B(q)\ge g_\alpha\,\mathrm{FB}$;
--   2. for every $\varepsilon>0$ there is a bilateral instance (one buyer, one seller, one edge $e$, $\mathcal F=\{\emptyset,\{e\}\}$) with finite-support priors on $[0,1]$ and $\mathrm{FB}>0$ on which every $q\in\mathcal P$ has $\mathcal G(q)+\alpha\,\mathcal B(q)\le(g_\alpha+\varepsilon)\,\mathrm{FB}$.
--
--   Differences from the source:
--   - encoding: $\inf_{\mathcal I}\mathcal L_{\mathcal I}(\alpha)/\mathrm{FB}(\mathcal I) = g_\alpha$, approached by bilateral instances → clause 1 (every instance reaches $g_\alpha\mathrm{FB}$) and clause 2 (bilateral instances with value at most $(g_\alpha+\varepsilon)\mathrm{FB}$), with $\mathcal L$ written through elements of $\mathcal P$; reason: equivalent since the maximum defining $\mathcal L$ is attained (Proposition 3.3); avoids division and a real `sSup`
--   - encoding: bilateral instance → `Market (Fin 1) (Fin 1)` with $E=\{(0,0)\}$ and $\mathcal F = \{\emptyset,\{(0,0)\}\}$; reason: the only bilateral instance shape with a possible trade
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 5.5, p.24 (proof in Section 5.3, pp.25–26)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_InPolytope
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_virtGFT
import Definitions.Def_SecondBestMatch_gCoeff
import Definitions.Def_SecondBestMatch_firstBestGFT

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 5.5** (tightness of the Beta coefficient; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §5.2, p.24). For every `α ≥ 0`,
`inf_{ℐ : FB(ℐ) > 0} ℒ_ℐ(α)/FB(ℐ) = g_α`, where the infimum is taken over all instances with
finite-support priors. Moreover, the infimum is approached by bilateral instances.

Clause (i) is the lower bound `ℒ_ℐ(α) ≥ g_α FB(ℐ)` (some `q ∈ 𝒫` reaches `g_α FB`); clause (ii)
says that for every `ε > 0` a bilateral instance (one buyer, one seller, one edge, `ℱ = {∅, {e}}`)
with finite-support priors and `FB > 0` has `ℒ(α) ≤ (g_α + ε) FB`.

**Formalization Note** `ℒ_ℐ(α) = max_{q ∈ 𝒫} (𝒢(q) + α ℬ(q))` is written through its maximizers, so
no supremum and no division appear. -/
theorem lemma_5_5 (α : ℝ) (hα : 0 ≤ α) :
    (∀ (B S : Type) [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S),
      IsUnitMarket m → IsFiniteSupportMarket m → 0 < firstBestGFT m →
        ∃ q, InPolytope m q ∧ gCoeff α * firstBestGFT m ≤ ordGFT m q + α * virtGFT m q) ∧
    (∀ ε : ℝ, 0 < ε → ∃ m : Market (Fin 1) (Fin 1),
      m.edges = {(0, 0)} ∧ m.family = {∅, {(0, 0)}} ∧ IsUnitMarket m ∧
        IsFiniteSupportMarket m ∧ 0 < firstBestGFT m ∧
        ∀ q, InPolytope m q → ordGFT m q + α * virtGFT m q ≤ (gCoeff α + ε) * firstBestGFT m) := by sorry

end SecondBestMatch
