-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_Supplement_theorem_5
-- name    : TwoSidedMatching.Statics.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:06:53.865797+00:00
-- url     : https://prove2.me/theorems/989051b8-8a99-470e-ad71-b1a1f7c8fd88
-- title:
--   Theorem 5 (corrected: nonnegative fixed seller costs) — all eight scale-family comparisons
-- statement:
--   Fix arbitrary positive buyer and seller arrival rates $\lambda^d,\lambda^s$ and horizon $T$. Each scale parameter $\theta>0$ specifies a distribution on its moving support, which may have an infinite upper endpoint. The CDF rescaling identity is $F_\theta(\theta x)=F_1(x)$ on the normalized support. All family members satisfy the weak virtual-value and virtual-cost regularity assumptions, and only the designated side changes.
--
--   For a buyer scale family with increasing generalized failure rate $vf^d_\theta(v)/(1-F^d_\theta(v))$, the buyer price and independently optimized profit increase for every $0<\theta_1\le\theta_2$. If the fixed seller distribution has nonnegative costs, the seller price and volume also increase. Thus, under that cost premise,
--
--   $$p^*_{\theta_1}\le p^*_{\theta_2},\quad w^*_{\theta_1}\le w^*_{\theta_2},\quad \mu^*_{\theta_1}\le\mu^*_{\theta_2},\quad \bar J^*_{\theta_1}\le\bar J^*_{\theta_2}.$$
--
--   For a seller scale family with decreasing generalized reverse failure rate $cf^s_\theta(c)/F^s_\theta(c)$, for every such ordered pair,
--
--   $$p^*_{\theta_1}\le p^*_{\theta_2},\quad w^*_{\theta_1}\le w^*_{\theta_2},\quad \mu^*_{\theta_2}\le\mu^*_{\theta_1},\quad \bar J^*_{\theta_2}\le\bar J^*_{\theta_1}.$$
--
--   These are all eight source comparisons. The statement also identifies the four quantities with the existing Statics quantities for a representation of every regular published Environment with nonnegative seller support. **Formalization Note** No continuity premise is assumed. Vanishing endpoint densities are allowed; virtual values are read at interior quantiles and extended by the supremum with zero. Failure-rate comparisons exclude zero denominators. Profit is always the value of the nonnegative-price program (D), not the fixed-price identity. The extra cost premise applies only to the volume and seller-price comparisons of part (i); buyer price and optimized profit retain the unrestricted fixed-seller domain; the negative-cost counterexample and source-proof evidence are in the local source audit. Infinite support endpoints are represented literally as extended-real quantiles, and profit as an extended-real supremum. All finite path profits are evaluated with real, integrable revenues, avoiding infinity subtraction. No tail moment or finiteness assumption restricts the source’s unbounded examples.
--
--   Differences from the source:
--   - correction: Theorem 5(i) does not explicitly require nonnegative fixed-side costs → require a nonnegative lower endpoint of the fixed seller distribution only for the seller-price and volume comparisons of part (i); reason: with fixed costs Uniform[-2,-1] and values Uniform[0,theta], the virtual-surplus volume (theta+2)/(2theta+2) and corresponding seller price both decrease; Supplemental Note p. 18 uses the missing nonnegativity of virtual cost
--   - reading: the scaling equality uses a normalized support and leaves density endpoint values implicit → move the physical support with theta, compare only defined failure-rate ratios, and take the interior virtual-surplus supremum with zero; reason: Online Appendix p. 7 and Supplemental Note pp. 17–19 specify scaling; the interior convention allows endpoint density zero without changing positive-width source thresholds
--   - generalization: the standing crossing assumption excludes markets whose minimum cost exceeds maximum value → keep every positive scale, setting the threshold to zero through an explicit singleton when supports do not cross; reason: the same supremum/quantile comparisons extend to the no-trade region and remove no crossing cases from the source
--   - encoding: private-value/cost distributions, including the unbounded examples of Online Appendix p. 7, and the fluid program (D) → use a minimal probability-law/density interface with possibly infinite endpoints and extended-real prices/profit, retain the independently optimized (D) value, and conclude representation of the published Statics interface on its domain; reason: the published density bundle additionally forces finite supports and positive endpoint densities; no continuity or tail moment assumption is imported, and infinite endpoints are never replaced by zero
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Online Appendix pp. 6–7, Theorem 5; Supplemental Note pp. 17–19, proof of Theorem 5

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Supplement_Scale

namespace TwoSidedMatching.Statics.Supplement

/-- Theorem 5 (corrected): all eight comparisons, no continuity premise.
Only the buyer-family volume and seller-price comparisons require nonnegative
fixed-side costs; buyer price and optimized profit retain the unrestricted domain. -/
theorem theorem_5 (lamD lamS T : ℝ)
    (hD : 0 < lamD) (hS : 0 < lamS) (hT : 0 < T) :
    (∀ M : ℝ → ScaleMarket,
      BuyerScaleFamily M → (∀ θ : ℝ, 0 < θ → (M θ).Regular ∧ BuyerIGFR (M θ).buyer) →
      ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
        scaleP (M θ₁) lamD lamS T ≤ scaleP (M θ₂) lamD lamS T ∧
        scaleValue (M θ₁) lamD lamS T ≤ scaleValue (M θ₂) lamD lamS T ∧
        (0 ≤ (M 1).seller.lo →
          scaleW (M θ₁) lamD lamS T ≤ scaleW (M θ₂) lamD lamS T ∧
          scaleMu (M θ₁) lamD lamS T ≤ scaleMu (M θ₂) lamD lamS T)) ∧
    (∀ M : ℝ → ScaleMarket,
      SellerScaleFamily M → (∀ θ : ℝ, 0 < θ → (M θ).Regular ∧ SellerDGRFR (M θ).seller) →
      ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
        scaleP (M θ₁) lamD lamS T ≤ scaleP (M θ₂) lamD lamS T ∧
        scaleW (M θ₁) lamD lamS T ≤ scaleW (M θ₂) lamD lamS T ∧
        scaleMu (M θ₂) lamD lamS T ≤ scaleMu (M θ₁) lamD lamS T ∧
        scaleValue (M θ₂) lamD lamS T ≤ scaleValue (M θ₁) lamD lamS T) ∧
    (∀ E : TwoSidedMatching.Statics.Environment, E.Regular → 0 ≤ E.loS →
      ∃ M : ScaleMarket, RepresentsEnvironment M E ∧
        scaleMu M lamD lamS T = TwoSidedMatching.Statics.muStar E lamD lamS T ∧
        scaleP M lamD lamS T = (TwoSidedMatching.Statics.pStar E lamD lamS T : EReal) ∧
        scaleW M lamD lamS T = (TwoSidedMatching.Statics.wStar E lamD lamS T : EReal) ∧
        scaleValue M lamD lamS T = (TwoSidedMatching.Statics.fluidValue E lamD lamS T : EReal)) := by sorry

end TwoSidedMatching.Statics.Supplement
