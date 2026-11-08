-- Prove2me | Theorems.Thm_SponsoredAssort_display_p28
-- name    : SponsoredAssort.display_p28
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:54:58.057575+00:00
-- url     : https://prove2.me/theorems/f3ab243d-8760-4687-a40a-f8161399b144
-- title:
--   Display, p.28 — $m^{\downarrow}$ is $1/n$-competitive for all revenues $r>0$
-- statement:
--   Let $r>0$ be any revenue vector and let $m^{\downarrow}$ be the partition mechanism of the singletons $\{\{1\},\dots,\{n\}\}$, for any choice of a welfare-maximizing singleton at each profile. Then
--
--   $$
--   \inf_{F\in\mathcal P(\mathbb R^n_+)}\ \frac{\mathbb E_{v\sim F}[R(m^{\downarrow},v)]}{\mathbb E_{v\sim F}[R(m^{FB},v)]}\ \ge\ \frac1n .
--   $$
--
--   No condition on the revenues is needed. With Corollary 5.3 this gives $\gamma^{PI}(r)\ge1/n$, the lower half of Proposition 5.4.
--
--   Differences from the source:
--   - encoding: infimum over all $F\in\mathcal P(\mathbb R^n_+)$ of a ratio of expectations → lower Lebesgue integrals in $[0,\infty]$, excluding the prior $\delta_0$; reason: the ratio is $0/0$ at $\delta_0$; the integrals agree with expectations for measurable integrands
--   - generalization: $m^{\downarrow}$ with the $\arg\max$ ties unresolved → every welfare-maximizing selector; reason: holds for every tie-breaking rule
--   - encoding: $m^{\downarrow}$ with payment (3) → payment by the rule after (3); reason: the allocation, hence the welfare, is the same
--   - generalization: standing order $r_1\ge\dots\ge r_n$ → any $r>0$; reason: the page states it for all revenues $r>0$; it specializes to the standing setting
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §5.3, display, p.28

import Mathlib
import Definitions.Def_SponsoredAssort_worstCaseRatio
import Definitions.Def_SponsoredAssort_IsBestSelector
import Definitions.Def_SponsoredAssort_partitionMech
import Definitions.Def_SponsoredAssort_singletons

open scoped NNReal ENNReal

namespace SponsoredAssort

/-- **Display on p.28** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), §5.3, p.28). For all
revenues `r > 0`, the singleton partition mechanism `m↓` satisfies
`inf_{F ∈ P(ℝⁿ₊)} E_{v∼F}[R(m↓, v)] / E_{v∼F}[R(m^FB, v)] ≥ 1/n`.

**Formalization Note.** `m↓` is `partitionMech r (singletons n) S` for any pointwise
welfare-maximizing selector `S` over the singletons. The infimum is `worstCaseRatio` (all priors
except the point mass at `0`, where the ratio is `0/0`). No order on the revenues is assumed. -/
theorem display_p28 {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (S : Attr n → Finset (Fin n)) (hS : IsBestSelector r (singletons n) S) :
    1 / (n : ℝ≥0∞) ≤ worstCaseRatio r (partitionMech r (singletons n) S) := by sorry

end SponsoredAssort
