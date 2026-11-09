-- Prove2me | Theorems.Thm_SecondBestMatch_lemma_4_3
-- name    : SecondBestMatch.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:57.245316+00:00
-- url     : https://prove2.me/theorems/ac11a7ec-6f4f-49bd-b9b6-12128f846c9e
-- title:
--   Lemma 4.3 — edge-level Lagrangian bound, and $g_\alpha > 1/2$
-- statement:
--   Let $F$ (buyer) and $G$ (seller) be finite-support Borel probability laws on $[0,1]$ with quantiles $Q_i$, $Q_j$ and discrete virtual value and cost $\phi_i$, $\psi_j$; let $D\subseteq(0,1)^2$ be a measurable down-set and $\alpha>0$. The edge-level randomized rule that retains the edge on $D_Z$, $Z\sim\mathrm{Beta}\big(\tfrac1{1+\alpha},\tfrac1{1+\alpha}\big)$, satisfies
--   $$
--   \mathbb E_Z\Big[\int_{D_Z}\Big(Q_i(\rho)-Q_j(\sigma)+\alpha\big(\phi_i(Q_i(\rho))-\psi_j(Q_j(\sigma))\big)\Big)d\rho\,d\sigma\Big]\ \ge\ g_\alpha\int_D\big(Q_i(\rho)-Q_j(\sigma)\big)\,d\rho\,d\sigma .
--   $$
--   Moreover, $g_\alpha>1/2$.
--
--   Differences from the source:
--   - generalization: $\mathcal D$ is the first-best selection region of one edge for fixed external reports in a finite-support instance → every measurable down-set $D$ of $(0,1)^2$ (`IsRankDownSet`) and every finite-support probability law on $[0,1]$; reason: the selection region is such a down-set (p.13) and the proof in Section 4.4 and Appendix E uses only the down-set property; the paper's statement is the special case
--   - encoding: $Q_i(\rho) = \sup\{v\in\mathrm{supp}(F_i) : \Pr[v_i\ge v]\ge\rho\}$, $Q_j(\sigma) = \inf\{c\in\mathrm{supp}(G_j):\Pr[c_j\le c]\ge\sigma\}$ → the published `buyerQuantile`/`sellerQuantile` (sup/inf over all reals); reason: for finite-support laws they agree on $(0,1)$, the only ranks integrated over
--   - encoding: $\mathbb E_Z$ for $Z\sim\mathrm{Beta}(1/(1+\alpha),1/(1+\alpha))$ → `betaExpect` (integral against the Beta density); reason: definition of the expectation
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Lemma 4.3, p.15

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Regularity
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regions
import Definitions.Def_SecondBestMatch_IsFiniteSupportLaw
import Definitions.Def_SecondBestMatch_discVirtualValue
import Definitions.Def_SecondBestMatch_discVirtualCost
import Definitions.Def_SecondBestMatch_gCoeff
import Definitions.Def_SecondBestMatch_betaExpect
import Definitions.Def_SecondBestMatch_contractRegion

open MeasureTheory Set Filter Topology MatchingGFT.TightE

namespace SecondBestMatch

/-- **Lemma 4.3** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.15). For every `α > 0`, the edge-level randomized rule that retains
`e` on `𝒟_Z` satisfies
`E_Z[∫_{𝒟_Z} (Qᵢ(ρ) − Qⱼ(σ) + α(φᵢ(Qᵢ(ρ)) − ψⱼ(Qⱼ(σ)))) dρ dσ] ≥ g_α ∫_𝒟 (Qᵢ(ρ) − Qⱼ(σ)) dρ dσ`.
Moreover, `g_α > 1/2`.

**Formalization Note** The paper states the bound for the selection region `𝒟` of one edge with
fixed external reports. It is stated here for every measurable down-set `D` of `(0, 1)²`
(`IsRankDownSet`), which contains that case; the proof in §4.4 and App. E uses only that `𝒟` is a
down-set. The prior is a finite-support Borel probability law on `[0, 1]`. Integrals are Lebesgue
integrals in `(ρ, σ)`; `E_Z` is `betaExpect` with `a = 1/(1+α)`. The buyer prior is `μ`, the seller prior `ν`. -/
theorem lemma_4_3 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsSupportedOnUnit μ) (hν : IsSupportedOnUnit ν) (hμfin : IsFiniteSupportLaw μ)
    (hνfin : IsFiniteSupportLaw ν) (D : Set (ℝ × ℝ)) (hD : IsRankDownSet D) (α : ℝ) (hα : 0 < α) :
    gCoeff α * ∫ p in D, (buyerQuantile μ p.1 - sellerQuantile ν p.2) ≤
        betaExpect (1 / (1 + α)) (1 / (1 + α)) (fun z =>
          ∫ p in contractRegion α z D,
            (buyerQuantile μ p.1 - sellerQuantile ν p.2 +
              α * (discVirtualValue μ (buyerQuantile μ p.1) -
                discVirtualCost ν (sellerQuantile ν p.2)))) ∧
      1 / 2 < gCoeff α := by sorry

end SecondBestMatch
