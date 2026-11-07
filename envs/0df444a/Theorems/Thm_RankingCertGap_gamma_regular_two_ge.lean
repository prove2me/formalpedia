-- Prove2me | Theorems.Thm_RankingCertGap_gamma_regular_two_ge
-- name    : RankingCertGap.gamma_regular_two_ge
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:12.861199+00:00
-- url     : https://prove2.me/theorems/ea1a0554-28e7-42e4-8e0e-ab89dbc83452
-- title:
--   Display (113), p.37 — $\tilde\gamma(2)\ge119/144$
-- statement:
--   Every cycle $C$ with $n\ge3$ offline and online nodes and any arrival order has $\mathrm{OPT}(C)=n$ and
--
--   $$
--   \frac{\mathbb E[\mathrm{RANKING}(C)]}{\mathrm{OPT}(C)}\ge\frac{119}{144}.
--   $$
--
--   The same inequality holds for $K_{2,2}$ and for every nonempty two-regular instance, and therefore
--
--   $$
--   \tilde\gamma(2)\ge\frac{119}{144}.
--   $$
--
--   This is the lower half of the exact competitiveness of RANKING on two-regular graphs.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), eq. (113), §10.2, p.37; pp.35–36

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_CycleInst

namespace RankingCertGap

/-- **Display (113).** Xu, arXiv:2610.17545 (held file sha256 75896dd9…), §10.2, p.37: "Since
`OPT(C) = n`, this proves `E[RANKING(C)]/OPT(C) ≥ 119/144`. The same inequality holds for `K_{2,2}` and
extends to every `G ∈ B₂` by summing over connected components. Thus `γ̃(2) ≥ 119/144`."

**Formalization Note.** The first conjunct is the cycle with `n ≥ 3`, the second is every instance of
`B₂` (including `K_{2,2}` and disconnected ones), and the third is (113). -/
theorem gamma_regular_two_ge :
    (∀ (n : ℕ), 3 ≤ n → ∀ t : Equiv.Perm (Fin n),
      (cycleInst t).OPT = n ∧
        (119 : ℝ) / 144 ≤ (cycleInst t).rankingValue / ((cycleInst t).OPT : ℝ)) ∧
    (∀ (m n : ℕ) (G : Inst m n), G.IsRegular 2 → 0 < G.OPT →
      (119 : ℝ) / 144 ≤ G.rankingValue / (G.OPT : ℝ)) ∧
    (119 : ℝ) / 144 ≤ gammaC (regular 2) := by sorry

end RankingCertGap
