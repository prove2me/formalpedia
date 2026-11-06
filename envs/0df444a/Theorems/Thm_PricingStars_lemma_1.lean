-- Prove2me | Theorems.Thm_PricingStars_lemma_1
-- name    : PricingStars.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:30:15.061179+00:00
-- url     : https://prove2.me/theorems/f16e26fb-daf0-470d-ae78-de4ab550130b
-- title:
--   Lemma 1 — price effect vs. selection effect: the induced review falls in $p$ iff $\kappa>1/2$
-- statement:
--   Let $\kappa\in[0,1)$, a true quality $\theta$ and an aggregate rating $\bar\psi$ be given, and write $\psi(p)$ for the induced average review (8) at price $p$.
--
--   1. For every price $p$, (9) holds: $\psi(p)=\theta+1-\bar\psi+p(1-2\kappa)$.
--   2. At every price, the marginal selection effect $\frac{d}{dp}\,\omega_e(\tilde\omega(\bar\psi,p))$ equals $1-\kappa$, the marginal direct price effect $\frac{d}{dp}(-\kappa p)$ equals $-\kappa$, and $\psi'(p)=1-2\kappa$ (10).
--   3. The direct price effect dominates the selection effect, $|-\kappa|>|1-\kappa|$, if and only if $\kappa>1/2$; for $\kappa<1/2$ the selection effect dominates, $|1-\kappa|>|-\kappa|$.
--   4. If $\kappa>1/2$, a price increase strictly decreases the induced average review: $\psi$ is strictly decreasing.
--   5. If $\kappa<1/2$, a price increase strictly increases it: $\psi$ is strictly increasing.
--
--   The lemma predicts the sign of the correlation between prices and reviews and drives the direction of the seller's dynamic price distortion.
--
--   Differences from the source:
--   - reading: 'the direct price effect dominates the selection effect' → |−κ| > |1 − κ|, the magnitudes of the two marginal effects of (10); reason: p.10 names −κ the marginal direct price effect and 1 − κ the marginal selection effect, and compares them
--   - generalization: the three claims of Lemma 1 → also (9) for every p and the derivatives of (10) at every p; reason: these are the displays the proof ('follows from the preceding discussion') rests on; the lemma's claims are included unchanged
--   - reading: the linear-quadratic model: q = 2(ψ̄ − p(1−κ)) (7) and the review (9), with no boundary solutions specified (footnote 5) → demand, cutoff and review are the paper's affine formulas on all of ℝ², prices are arbitrary reals, nothing is clamped to [0,1]; reason: the paper solves exactly this unconstrained problem (its remarks that flow profits are bounded, pp.12 and 24, do not hold for these formulas and are not used); with clamping the value function is not quadratic and (28)–(29) are not derived
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), Lemma 1, p.11 (PDF 13), with (8)–(10), p.10 (PDF 12)

import Mathlib
import Definitions.Def_PricingStars_Model

namespace PricingStars

/-- Lemma 1 (Price & Selection Effect) (Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224
DP No. 143 (Jan 2020), p.11 (PDF 13); with (8)–(10), p.10 (PDF 12)). For `κ ∈ [0,1)`, true
quality `θ` and aggregate rating `ψ̄`:
1. (9): the induced average review is `θ + 1 − ψ̄ + p(1 − 2κ)` for every price `p`;
2. (10): at every price the marginal selection effect `d ω_e(ω̃(ψ̄, p))/dp` equals `1 − κ`, the
   marginal direct price effect `d(−κp)/dp` equals `−κ`, and the induced review has derivative
   `1 − 2κ`;
3. the direct price effect dominates the selection effect (`|−κ| > |1 − κ|`) iff `κ > 1/2`, and the
   selection effect dominates (`|1 − κ| > |−κ|`) when `κ < 1/2`;
4. if `κ > 1/2` the induced review is strictly decreasing in the price;
5. if `κ < 1/2` it is strictly increasing in the price.

**Formalization Note** "Dominates" compares the magnitudes of the two marginal effects of (10).
The model is the paper's unclamped linear one. -/
theorem lemma_1 (θ κ ψ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    (∀ p : ℝ, inducedReview θ κ ψ p = θ + 1 - ψ + p * (1 - 2 * κ)) ∧
    (∀ p : ℝ, HasDerivAt (fun x => avgTaste (cutoff κ ψ x)) (1 - κ) p ∧
      HasDerivAt (fun x => -κ * x) (-κ) p ∧
      HasDerivAt (inducedReview θ κ ψ) (1 - 2 * κ) p) ∧
    (|1 - κ| < |-κ| ↔ 1 / 2 < κ) ∧
    (κ < 1 / 2 → |-κ| < |1 - κ|) ∧
    (1 / 2 < κ → StrictAnti (inducedReview θ κ ψ)) ∧
    (κ < 1 / 2 → StrictMono (inducedReview θ κ ψ)) := by sorry

end PricingStars
