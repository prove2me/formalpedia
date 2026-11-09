-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_4_5
-- name    : SecondBestMatch.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:23.6702+00:00
-- url     : https://prove2.me/theorems/f18aa15b-c50d-4cd6-8ab3-0d0abc8c1bab
-- title:
--   Lemma 4.5 — seller-side contraction bound
-- statement:
--   Let $G$ be a finite-support Borel probability law on $[0,1]$ with lower-tail quantile $Q$ and discrete virtual cost $\psi$, let $D\subseteq(0,1)^2$ be a measurable down-set, and let $\alpha>0$. With $Z\sim\mathrm{Beta}\big(\tfrac1{1+\alpha},\tfrac1{1+\alpha}\big)$ and the contracted region $D_Z$,
--   $$
--   \mathbb E_Z\Big[\int_{D_Z}\big(Q(\sigma)+\alpha\,\psi(Q(\sigma))\big)\,d\rho\,d\sigma\Big]\ \le\ g_\alpha\int_D Q(\sigma)\,d\rho\,d\sigma .
--   $$
--
--   Differences from the source:
--   - generalization: $\mathcal D$ is the first-best selection region of one edge for fixed external reports in a finite-support instance → every measurable down-set $D$ of $(0,1)^2$ (`IsRankDownSet`) and every finite-support probability law on $[0,1]$; reason: the selection region is such a down-set (p.13) and the proof in Section 4.4 and Appendix E uses only the down-set property; the paper's statement is the special case
--   - encoding: $Q_i(\rho) = \sup\{v\in\mathrm{supp}(F_i) : \Pr[v_i\ge v]\ge\rho\}$, $Q_j(\sigma) = \inf\{c\in\mathrm{supp}(G_j):\Pr[c_j\le c]\ge\sigma\}$ → the published `buyerQuantile`/`sellerQuantile` (sup/inf over all reals); reason: for finite-support laws they agree on $(0,1)$, the only ranks integrated over
--   - encoding: $\mathbb E_Z$ for $Z\sim\mathrm{Beta}(1/(1+\alpha),1/(1+\alpha))$ → `betaExpect` (integral against the Beta density); reason: definition of the expectation
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 4.5, p.15 (proof in Appendix E, pp.37–38)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Regularity
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regions
import Definitions.Def_SecondBestMatch_IsFiniteSupportLaw
import Definitions.Def_SecondBestMatch_discVirtualCost
import Definitions.Def_SecondBestMatch_gCoeff
import Definitions.Def_SecondBestMatch_betaExpect
import Definitions.Def_SecondBestMatch_contractRegion

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 4.5** (seller-side contraction bound; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.15). For every `α > 0`,
`E_Z[∫_{𝒟_Z} (Qⱼ(σ) + α ψⱼ(Qⱼ(σ))) dρ dσ] ≤ g_α ∫_𝒟 Qⱼ(σ) dρ dσ`.

**Formalization Note** The paper states the bound for the selection region `𝒟` of one edge with
fixed external reports. It is stated here for every measurable down-set `D` of `(0, 1)²`
(`IsRankDownSet`), which contains that case; the proof in §4.4 and App. E uses only that `𝒟` is a
down-set. The prior is a finite-support Borel probability law on `[0, 1]`. Integrals are Lebesgue
integrals in `(ρ, σ)`; `E_Z` is `betaExpect` with `a = 1/(1+α)`. -/
theorem lemma_4_5 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : IsSupportedOnUnit ν)
    (hfin : IsFiniteSupportLaw ν) (D : Set (ℝ × ℝ)) (hD : IsRankDownSet D) (α : ℝ) (hα : 0 < α) :
    betaExpect (1 / (1 + α)) (1 / (1 + α)) (fun z =>
        ∫ p in contractRegion α z D,
          (sellerQuantile ν p.2 + α * discVirtualCost ν (sellerQuantile ν p.2))) ≤
      gCoeff α * ∫ p in D, sellerQuantile ν p.2 := by sorry

end SecondBestMatch
