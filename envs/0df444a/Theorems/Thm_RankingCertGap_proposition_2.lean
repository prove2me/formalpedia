-- Prove2me | Theorems.Thm_RankingCertGap_proposition_2
-- name    : RankingCertGap.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:55:24.074883+00:00
-- url     : https://prove2.me/theorems/dda16c23-5847-40b1-81c0-9ea98429a931
-- title:
--   Proposition 2, p.4 — strict certifying gaps at degree two
-- statement:
--   Let $\gamma(2)$ and $\tilde\gamma(2)$ be the competitiveness of RANKING on instances of online degree at most two and on nonempty two-regular instances. Let $\Gamma_{\mathcal A}(2)$ and $\tilde\Gamma_{\mathcal A}(2)$ be the certifying capacities of the rank-dependent gain-sharing protocol on these classes over the full class $\mathcal A$ of Borel gain-sharing functions. Then
--
--   $$
--   \Gamma_{\mathcal A}(2)<\frac{715361}{10^6}<\gamma(2),\qquad\tilde\Gamma_{\mathcal A}(2)=\frac34<\frac{119}{144}=\tilde\gamma(2).
--   $$
--
--   Thus the protocol is not tight for RANKING on either class, even when the gain-sharing function ranges over all of $\mathcal A$. The gaps therefore come from the rank-dependent splitting rule and its edgewise certificate, not from a suboptimal choice of function or from imposing monotonicity or continuity.
--
--   Differences from the source:
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - encoding: $f:[0,1]\to[0,1]$ → $f:\mathbb R\to\mathbb R$ with values in $[0,1]$ everywhere; reason: a printed $f$ extends (for instance by $0$), and scores read $f$ only on $[0,1]$ almost surely; same suprema and scores
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Proposition 2, eq. (9), p.4; App. M.1, pp.86–87

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity

namespace RankingCertGap

/-- **Proposition 2 (Strict certifying gaps at degree two).** Xu, *Certifying Capacity and Gaps of the
Rank-Dependent Gain-Sharing Framework for Ranking*, arXiv:2610.17545 (held file sha256 75896dd9…),
Proposition 2, p.4: "One has `Γ_𝒜(2) < 715361/10⁶ < γ(2)`, `Γ̃_𝒜(2) = 3/4 < 119/144 = γ̃(2)`. (9)
Thus the rank-dependent protocol `𝔓` is not tight for RANKING on either `B^on_≤2` or `B₂`, even when
the gain-sharing function ranges over the full admissible class `𝒜`."

**Formalization Note.** All infima and suprema are real `sInf`/`sSup` over nonempty bounded sets; the
verification file proves it. The last two conjuncts are the non-tightness sentence. -/
theorem proposition_2 :
    GammaC classA (onDegLE 2) < 715361 / 10 ^ 6 ∧
    (715361 : ℝ) / 10 ^ 6 < gammaC (onDegLE 2) ∧
    GammaC classA (regular 2) = 3 / 4 ∧
    (3 : ℝ) / 4 < 119 / 144 ∧
    gammaC (regular 2) = 119 / 144 ∧
    ¬ IsTight classA (onDegLE 2) ∧
    ¬ IsTight classA (regular 2) := by sorry

end RankingCertGap
