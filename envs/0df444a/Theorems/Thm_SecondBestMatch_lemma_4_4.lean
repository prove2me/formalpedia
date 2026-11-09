-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_4_4
-- name    : SecondBestMatch.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:24.976201+00:00
-- url     : https://prove2.me/theorems/76439313-8ed7-4f4c-9353-b8ccd130f87b
-- title:
--   Lemma 4.4 — buyer-side contraction bound
-- statement:
--   Let $F$ be a finite-support Borel probability law on $[0,1]$ with upper-tail quantile $Q$ and discrete virtual value $\phi$, let $D\subseteq(0,1)^2$ be a measurable down-set, and let $\alpha>0$. With $Z\sim\mathrm{Beta}\big(\tfrac1{1+\alpha},\tfrac1{1+\alpha}\big)$ and the contracted region $D_Z$,
--   $$
--   \mathbb E_Z\Big[\int_{D_Z}\big(Q(\rho)+\alpha\,\phi(Q(\rho))\big)\,d\rho\,d\sigma\Big]\ \ge\ g_\alpha\int_D Q(\rho)\,d\rho\,d\sigma .
--   $$
--
--   Differences from the source:
--   - generalization: $\mathcal D$ is the first-best selection region of one edge for fixed external reports in a finite-support instance → every measurable down-set $D$ of $(0,1)^2$ (`IsRankDownSet`) and every finite-support probability law on $[0,1]$; reason: the selection region is such a down-set (p.13) and the proof in Section 4.4 and Appendix E uses only the down-set property; the paper's statement is the special case
--   - encoding: $Q_i(\rho) = \sup\{v\in\mathrm{supp}(F_i) : \Pr[v_i\ge v]\ge\rho\}$, $Q_j(\sigma) = \inf\{c\in\mathrm{supp}(G_j):\Pr[c_j\le c]\ge\sigma\}$ → the published `buyerQuantile`/`sellerQuantile` (sup/inf over all reals); reason: for finite-support laws they agree on $(0,1)$, the only ranks integrated over
--   - encoding: $\mathbb E_Z$ for $Z\sim\mathrm{Beta}(1/(1+\alpha),1/(1+\alpha))$ → `betaExpect` (integral against the Beta density); reason: definition of the expectation
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 4.4, p.15 (proof in Section 4.4, pp.19–20)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Regularity
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regions
import Definitions.Def_SecondBestMatch_IsFiniteSupportLaw
import Definitions.Def_SecondBestMatch_discVirtualValue
import Definitions.Def_SecondBestMatch_gCoeff
import Definitions.Def_SecondBestMatch_betaExpect
import Definitions.Def_SecondBestMatch_contractRegion

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 4.4** (buyer-side contraction bound; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.15). For every `α > 0`,
`E_Z[∫_{𝒟_Z} (Qᵢ(ρ) + α φᵢ(Qᵢ(ρ))) dρ dσ] ≥ g_α ∫_𝒟 Qᵢ(ρ) dρ dσ`.

**Formalization Note** The paper states the bound for the selection region `𝒟` of one edge with
fixed external reports. It is stated here for every measurable down-set `D` of `(0, 1)²`
(`IsRankDownSet`), which contains that case; the proof in §4.4 and App. E uses only that `𝒟` is a
down-set. The prior is a finite-support Borel probability law on `[0, 1]`. Integrals are Lebesgue
integrals in `(ρ, σ)`; `E_Z` is `betaExpect` with `a = 1/(1+α)`. -/
theorem lemma_4_4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsSupportedOnUnit μ)
    (hfin : IsFiniteSupportLaw μ) (D : Set (ℝ × ℝ)) (hD : IsRankDownSet D) (α : ℝ) (hα : 0 < α) :
    gCoeff α * ∫ p in D, buyerQuantile μ p.1 ≤
      betaExpect (1 / (1 + α)) (1 / (1 + α)) fun z =>
        ∫ p in contractRegion α z D,
          (buyerQuantile μ p.1 + α * discVirtualValue μ (buyerQuantile μ p.1)) := by sorry

end SecondBestMatch
