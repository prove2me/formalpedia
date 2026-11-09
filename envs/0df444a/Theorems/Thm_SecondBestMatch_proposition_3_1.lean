-- Prove2me | Theorems.Thm_SecondBestMatch_proposition_3_1
-- name    : SecondBestMatch.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:45.061434+00:00
-- url     : https://prove2.me/theorems/9d13740b-40fe-46c7-a249-35f871a26abc
-- title:
--   Proposition 3.1 — finite-support reduction
-- statement:
--   Fix $\beta\in[0,1]$. Suppose that $\mathrm{SB}(\mathcal J)\ge\beta\,\mathrm{FB}(\mathcal J)$ for every instance $\mathcal J$ with mutually independent finite-support priors. Then $\mathrm{SB}(\mathcal I)\ge\beta\,\mathrm{FB}(\mathcal I)$ for every instance $\mathcal I$ with mutually independent Borel priors on $[0,1]$. Consequently,
--   $$
--   \inf_{\substack{\mathcal I\ \text{Borel priors}\\ \mathrm{FB}(\mathcal I)>0}}\frac{\mathrm{SB}(\mathcal I)}{\mathrm{FB}(\mathcal I)}
--   =\inf_{\substack{\mathcal J\ \text{finite-support priors}\\ \mathrm{FB}(\mathcal J)>0}}\frac{\mathrm{SB}(\mathcal J)}{\mathrm{FB}(\mathcal J)} .
--   $$
--
--   Differences from the source:
--   - encoding: infima over all instances → infima over instances with buyers `Fin n` and sellers `Fin k`; reason: every instance is a relabelling of one of these and SB, FB are invariant under relabelling
--   - encoding: finitely many buyers and sellers → finite types `B`, `S` (`Fintype`); reason: Lean convention; same instances
--   - encoding: allocation rules are Borel kernels $[0,1]^K\to\Delta(\mathcal F)$ and all transfer expectations are finite and well defined (standing assumption, p.8) → fields of `IsAdmissible` (measurable allocation that is a distribution over $\mathcal F$ on $[0,1]^K$; integrable transfers, also with the agent's own report fixed); reason: the paper's standing convention made explicit; same mechanisms
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Proposition 3.1, p.10 (proof in Appendix C, pp.33–36)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_firstBestGFT
import Definitions.Def_SecondBestMatch_secondBest

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Proposition 3.1** (finite-support reduction; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.1, p.10). Fix `β ∈ [0, 1]`. Suppose
that `SB(𝒥) ≥ β FB(𝒥)` for every instance `𝒥` with mutually independent finite-support priors.
Then `SB(ℐ) ≥ β FB(ℐ)` for every instance `ℐ` with mutually independent Borel priors on `[0, 1]`.
Consequently the infimum of `SB/FB` over instances with Borel priors and `FB > 0` equals the
infimum over instances with finite-support priors and `FB > 0`.

**Formalization Note** Instances range over all finite agent types in the first clause; in the
infima they range over `Fin n` buyers and `Fin k` sellers, which covers every instance up to
relabelling (`SB` and `FB` are invariant under it). Both sets of ratios are nonempty and bounded
below by `0`. -/
theorem proposition_3_1 :
    (∀ β : ℝ, β ∈ Icc (0 : ℝ) 1 →
      (∀ (B' S' : Type) [Fintype B'] [Fintype S'] [DecidableEq B'] [DecidableEq S']
          (m' : Market B' S'), IsUnitMarket m' → IsFiniteSupportMarket m' →
            β * firstBestGFT m' ≤ secondBest m') →
      ∀ (B S : Type) [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S),
        IsUnitMarket m → β * firstBestGFT m ≤ secondBest m) ∧
    sInf {r : ℝ | ∃ (n k : ℕ) (m : Market (Fin n) (Fin k)),
        IsUnitMarket m ∧ 0 < firstBestGFT m ∧ r = secondBest m / firstBestGFT m} =
      sInf {r : ℝ | ∃ (n k : ℕ) (m : Market (Fin n) (Fin k)),
        IsUnitMarket m ∧ IsFiniteSupportMarket m ∧ 0 < firstBestGFT m ∧
          r = secondBest m / firstBestGFT m} := by sorry

end SecondBestMatch
