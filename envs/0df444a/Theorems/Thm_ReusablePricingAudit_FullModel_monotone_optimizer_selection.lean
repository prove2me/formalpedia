-- Prove2me | Theorems.Thm_ReusablePricingAudit_FullModel_monotone_optimizer_selection
-- name    : ReusablePricingAudit.FullModel.monotone_optimizer_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:50:19.479348+00:00
-- url     : https://prove2.me/theorems/e28e84bf-61c5-4116-bf55-ea7709fcb657
-- title:
--   Lemma 1 (corrected: selection of an optimizer)
-- statement:
--   Fix a resource instance. Suppose a feasible stationary rate vector $\lambda^{\mathrm{opt}}$ attains the maximum of the stationary weighted objective, and a feasible rate $\bar\lambda$ attains the maximum of the myopic objective $l(\alpha_1(p(l)-c)+\alpha_2)$, with zero reward at the no-offer action. Then there exists a feasible stationary vector $\lambda^*$ such that
--   $$W(\lambda^*)=W(\lambda^{\mathrm{opt}}),\qquad
--   \bar\lambda\ge\lambda_C^*\ge\cdots\ge\lambda_1^*.$$
--   The chain holds at every inventory state, including unreachable states. Ordinary concavity and weights in the closed simplex suffice; strict concavity and $\alpha_1>0$ are not hypotheses.
--
--   This records the monotone selection used by the companion's construction. It assumes the two maximizers explicitly denoted in the source, rather than asserting that every possible endpoint model has such maximizers. No restriction is imposed on the main guarantee's instances.
--
--   Differences from the source:
--   - correction: every arbitrary optimal rate vector obeys the chain in Lemma 1 → an optimal stationary vector can be selected with the entire chain and the same optimal value; reason: for C=3, μ=Λ=c=1, uniform demand p(l)=1-l, and α=(0,0,1), the vector (1,0,0) is optimal with all mass at free state 3 but violates λ₂≥λ₁; the all-zero optimal vector obeys the chain
--   - encoding: a rate-zero no-purchase action, possibly at an infinite limiting price → an explicit no-offer action with zero transaction reward and an ignored dummy price at zero; reason: all positive-rate inverse prices are retained, including unbounded limits at zero
--   - reading: N is called an offered-arrival process on p. 8 but units sold on p. 9 and Eq. (6) → market share counts accepted sales D, separately from potential arrivals A and willing arrivals B; reason: with C=μ=Λ=c=1 and uniform demand at rate 1 the offered rate is 1 and sales rate is 1/2; units sold and Eq. (6) select D
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3 (11 February 2020), p. 11, Lemma 1, (8); pp. ec3–ec5 (PDF 24–26), proof in §EC.2

import Mathlib
import Definitions.Def_ReusablePricingAudit_FullModel_ResourceModel
import Definitions.Def_StaticReusable_Guarantee_Setting

namespace ReusablePricingAudit.FullModel

/-- Lemma 1, corrected only to select an optimizer, rather than constrain tied
or unreachable-state choices of an arbitrary optimizer. An attained stationary
optimum and a myopic maximizer are supplied as in the source's notation. -/
theorem monotone_optimizer_selection (I : ResourceInstance)
    (lamOpt : StationaryRates I)
    (hopt : ∀ lam : StationaryRates I,
      StaticReusable.Guarantee.value I.C I.μ (auxiliaryPrice I) I.c I.α₁ I.α₂ I.α₃
        (fun j => (lam j).val) ≤
      StaticReusable.Guarantee.value I.C I.μ (auxiliaryPrice I) I.c I.α₁ I.α₂ I.α₃
        (fun j => (lamOpt j).val))
    (lbar : Rate I)
    (hmyopic : ∀ l : Rate I,
      StaticReusable.Guarantee.myopic (auxiliaryPrice I) I.c I.α₁ I.α₂ l.val ≤
      StaticReusable.Guarantee.myopic (auxiliaryPrice I) I.c I.α₁ I.α₂ lbar.val) :
    ∃ lam : StationaryRates I,
      StaticReusable.Guarantee.value I.C I.μ (auxiliaryPrice I) I.c I.α₁ I.α₂ I.α₃
        (fun j => (lam j).val) =
      StaticReusable.Guarantee.value I.C I.μ (auxiliaryPrice I) I.c I.α₁ I.α₂ I.α₃
        (fun j => (lamOpt j).val) ∧
      (lam I.C).val ≤ lbar.val ∧
      ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ I.C → (lam i).val ≤ (lam j).val := by sorry

end ReusablePricingAudit.FullModel
