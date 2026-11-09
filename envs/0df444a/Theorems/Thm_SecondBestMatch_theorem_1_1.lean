-- Prove2me | Theorems.Thm_SecondBestMatch_theorem_1_1
-- name    : SecondBestMatch.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:20.044674+00:00
-- url     : https://prove2.me/theorems/f8d19fd2-1b88-466a-82b3-3cd1ebb1930f
-- title:
--   Theorem 1.1 — $\mathrm{SB}\ge\frac12\mathrm{FB}$ for every matching market, and $1/2$ is tight
-- statement:
--   Consider matching markets with finitely many unit-demand buyers $B$ and unit-supply sellers $S$, trading edges $E\subseteq B\times S$, a nonempty downward-closed family $\mathcal F$ of matchings, and mutually independent Borel priors on $[0,1]$. Let $\mathrm{FB}$ be the expected first-best welfare and $\mathrm{SB}$ the supremum of the gains from trade of mechanisms that are BIC and interim IR on the full report domain and exactly strongly budget balanced at every report profile.
--
--   1. For every instance $\mathcal I$,
--   $$
--   \mathrm{SB}(\mathcal I)\ \ge\ \tfrac12\,\mathrm{FB}(\mathcal I).
--   $$
--   2. The ratio is tight: for every $\varepsilon>0$ there is an instance with $\mathrm{FB}>0$ on which every BIC, interim-IR, exactly strongly budget-balanced mechanism has gains from trade at most $\big(\tfrac12+\varepsilon\big)\mathrm{FB}$.
--
--   This is the exact worst-case efficiency of the second best over the class of downward-closed matching markets.
--
--   Differences from the source:
--   - reading: Theorem 1.1 (informal): for every instance SB ≥ ½FB, and this ratio is tight → clause 1 for every instance of the Section 2 model, and clause 2: for every ε > 0 an instance with FB > 0 on which every feasible mechanism has GFT ≤ (½ + ε)FB; reason: the informal statement means $\inf_{\mathrm{FB}>0}\mathrm{SB}/\mathrm{FB} = 1/2$ over the model of Section 2 ("Proposition 3.1 and Theorem 4.10, together with the tight examples …, show that γ(0) = 1/2", p.22); clause 2 is the ≤ half
--   - encoding: SB ≤ (½ + ε)FB → every second-best feasible mechanism has GFT ≤ (½ + ε)FB; reason: equivalent for a supremum; does not rest on a real `sSup`
--   - encoding: finitely many buyers and sellers → finite types `B`, `S` in clause 1, `Fin n`, `Fin k` in clause 2; reason: Lean convention; same instances up to relabelling
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Theorem 1.1 (informal), p.4; formal model Section 2, pp.7–9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsSBFeasible
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_firstBestGFT
import Definitions.Def_SecondBestMatch_secondBest

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Theorem 1.1** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §1.1, p.4). For every matching-market instance `ℐ`, `SB(ℐ) ≥ ½ FB(ℐ)`.
Moreover, this ratio is tight.

Clause (a): for every instance (finite buyers and sellers, trading edges `E`, a nonempty
downward-closed family `ℱ` of matchings, mutually independent Borel priors on `[0, 1]`),
`SB ≥ ½ FB`. Clause (b): for every `ε > 0` there is an instance with `FB > 0` on which every BIC,
interim-IR, exactly strongly budget-balanced mechanism has `GFT ≤ (½ + ε) FB`.

**Formalization Note** The informal theorem is made precise by the model of §2 (pp.7–9). Tightness
is written as a bound on every feasible mechanism instead of on `SB`, which is the same (the
supremum is at most `(½ + ε) FB` iff every element is) and does not rest on a real `sSup`. -/
theorem theorem_1_1 :
    (∀ {B S : Type} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S),
      IsUnitMarket m → 1 / 2 * firstBestGFT m ≤ secondBest m) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (n k : ℕ) (m : Market (Fin n) (Fin k)),
      IsUnitMarket m ∧ 0 < firstBestGFT m ∧
        ∀ A : Mechanism (Fin n) (Fin k), IsSBFeasible m A →
          ordGFT m A.alloc ≤ (1 / 2 + ε) * firstBestGFT m) := by sorry

end SecondBestMatch
