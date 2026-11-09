-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_majority_amplification
-- name    : WatsonPseudodeterminism.MASeparation.majority_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:41.448057+00:00
-- url     : https://prove2.me/theorems/bc02c9e5-1644-44b2-9020-8f35c6f347af
-- title:
--   §4 — Majority amplification (corrected: d ≥ 2)
-- statement:
--   Let $D$ be a distribution over deterministic protocols of depth at most $d$, where $d\ge2$. Let $D'_d$ be the constructed law of the strict majority of $2d$ independent runs, with ties outputting zero. Then its support has depth at most $2d^2$, and for every input pair,
--
--   $$D(x,y)\ge0.99\Rightarrow D'_d(x,y)\ge1-0.01\,2^{-d},\qquad D(x,y)\le0.01\Rightarrow D'_d(x,y)\le0.01\,2^{-d}.$$
--
--   Consequently, any $0.01$-error protocol for a partial function becomes a $0.01\,2^{-d}$-error protocol on its valid inputs. The cost guarantee concerns the actual sequential majority tree, rather than an unspecified distribution with the desired acceptance probabilities.
--
--   Differences from the source:
--   - correction: the majority claim is printed without an explicit small-d restriction → d ≥ 2; reason: at d=1 and D(x,y)=0.99 on a one-input, strict majority of two accepts with probability 0.9801, giving error 0.0199 > 0.005; the printed large-size application has d ≥ 2
--   - encoding: majority vote with no stated tie rule → strict majority, with ties outputting zero; reason: this specifies the construction; the claimed error bound holds with this rule for d ≥ 2
--   - generalization: error guarantee on the valid inputs of the partial F′ → pointwise implications on every input of arbitrary X and Y; reason: restricting to the valid inputs and their corresponding thresholds recovers both source error clauses
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §4, preprocessing phase, p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Majority

namespace WatsonPseudodeterminism.MASeparation

/-- §4, p. 11 (corrected: d ≥ 2).
For d=1 and acceptance 0.99, strict majority of two runs accepts with probability
0.9801, giving error 0.0199 > 0.005. The actual law below uses ties to false. -/
theorem majority_amplification (X Y : Type) (D : RandomProtocol X Y)
    (d : ℕ) (hd : 2 ≤ d) (hdepth : DepthBound D d) :
    DepthBound (majorityLaw D d) (2 * d ^ 2) ∧
    ∀ x y,
      ((0.99 : ℝ) ≤ acceptance D x y →
        1 - (0.01 : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) ≤ acceptance (majorityLaw D d) x y) ∧
      (acceptance D x y ≤ (0.01 : ℝ) →
        acceptance (majorityLaw D d) x y ≤ (0.01 : ℝ) * (2 : ℝ) ^ (-(d : ℝ))) := by sorry

end WatsonPseudodeterminism.MASeparation
