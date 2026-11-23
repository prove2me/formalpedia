-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_Supplement_theorem_8_1_NP_complete
-- name    : PLCMarkets.ExactCover.Supplement.theorem_8_1_NP_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:23:40.314037+00:00
-- url     : https://prove2.me/theorems/94217714-4995-45e6-87f4-74b9ac962f13
-- title:
--   THEOREM 8.1 — existence of an exact or $\nu_8^{-5}$-approximate equilibrium is NP-complete for Fisher and Arrow–Debreu markets
-- statement:
--   Consider markets with additively separable piecewise-linear concave utilities and rational data, given by their binary codes, with no further condition. For a market with $a$ agents let $\nu_8(a)=\max(1,\lceil(a-2)/2\rceil)$, so $\nu_8(2n+2)=n$. Each of the following four languages over $\{0,1\}$ is NP-complete:
--
--   1. codes of Fisher markets that have a price equilibrium;
--   2. codes of Arrow–Debreu markets that have a price equilibrium;
--   3. codes of Fisher markets with $a$ buyers that have an $\varepsilon$-approximate equilibrium;
--   4. codes of Arrow–Debreu markets with $a$ agents that have an $\varepsilon$-approximate equilibrium;
--
--   where in 3 and 4
--   $$\varepsilon=\nu_8(a)^{-5}.$$
--   NP-complete means the language is in NP and every language in NP reduces to it by a polynomial-time many-one reduction.
--
--   The theorem shows that, without a sufficient condition such as (C') or (C2), even deciding whether an equilibrium exists is intractable unless P = NP, in contrast with Theorems 6.1 and 7.1.
--
--   **Formalization Note** NP and NP-completeness are the published `CookPvsNP.NP` and `CookPvsNP.NPComplete` (Cook's Turing machines, polynomial-time many-one reductions from languages over every finite nonempty alphabet). Strings that are not the code of a market with nonempty agents and goods (and, for Arrow–Debreu markets, positive total supplies) are not in the languages. The equilibrium notions are those of the `SourceEquilibrium` item.
--
--   Differences from the source:
--   - reading: ε = O(n^-5), n the size of the X3C instance (§8, p. 10:19) → ε = ν₈(a)^-5 with ν₈(a) = max(1, ⌈(a − 2)/2⌉) for a market with a agents; reason: Lemma 8.3 fixes ε = n^-5 with coefficient 1 (p. 10:21); its markets have 2n + 2 agents, where ν₈(a) = n, and ν₈ is defined on every market
--   - encoding: the problem of determining whether a given market has an (approximate) equilibrium → four languages of binary codes of markets, each CookPvsNP.NPComplete; strings that do not code a market with nonempty agent and good sets are not members; reason: a decision problem is a language of codes; the degenerate strings are fixed no-instances
--   - reading: each good totals 1 unit, without loss of generality (§5, p. 10:9; §6, p. 10:10) → Arrow–Debreu instances are markets whose goods all have positive total supply; reason: the normalization applies to every such market; the source's input class is the markets given, before normalization
--   - encoding: Arrow–Debreu optimal bundles → the budget maximization of §6, p. 10:10, not the §8 mission's IsOptimalBundle with its cap on purchases of flat goods; reason: the general theorem uses the paper's general definition
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:19, THEOREM 8.1 (X3C reduction and ε = n^-5: pp. 10:19–10:23)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_Supplement_Problems

namespace PLCMarkets.ExactCover.Supplement

theorem theorem_8_1_NP_complete :
    CookPvsNP.NPComplete fisherExistenceLang ∧ CookPvsNP.NPComplete adExistenceLang ∧
      CookPvsNP.NPComplete fisherApproxExistenceLang ∧
        CookPvsNP.NPComplete adApproxExistenceLang := by sorry

end PLCMarkets.ExactCover.Supplement
