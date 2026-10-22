-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_lemma1_myopicPrice_monotone
-- name    : ReferencePricing.Myopic.lemma1_myopicPrice_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:37:21.511396+00:00
-- url     : https://prove2.me/theorems/1ebb04d2-6432-4d49-8d60-343df78f51be
-- title:
--   Lemma 1 — the myopic (single-period profit-maximizing) price p̃(r) is increasing in r
-- statement:
--   Under the standing assumptions of §4 — $\bar p > 0$, Assumptions 1, 2 and 3, $R(0,r)=0$, and $d$ differentiable — the single-period profit-maximizing price
--   $$\tilde p(r) = \operatorname*{arg\,max}_{p \in P} \Pi(p, r)$$
--   (the largest maximizer) is increasing in $r$ on $P = [0, \bar p]$.
--
--   A myopic firm charges more when consumers expect higher prices. The paper obtains this from supermodularity of the profit (Assumption 3(c)) through Topkis' monotonicity theorem; it drives the monotone behaviour of the myopic path.
--
--   **Formalization Note.** Assumptions 2 and 3 are standing throughout §§4.1–4.3 and are kept as hypotheses. Differentiability of $d$ is added: Assumption 3(b) refers to $\pi'$, and Lean's `deriv` is $0$ at points of non-differentiability.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 418, Lemma 1

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

namespace ReferencePricing.Myopic

/-- Lemma 1 (p. 418): under the standing assumptions of §4 (Assumptions 1–3), the single-period
profit-maximizing price `p̃(r) = argmax_{p ∈ P} Π(p, r)` (largest maximizer) is increasing in `r`
on `P = [0, p̄]`. -/
theorem lemma1_myopicPrice_monotone (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ)
    (hpbar : 0 < pbar) (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    MonotoneOn (myopicPrice (profit d R) pbar) (Set.Icc 0 pbar) := by sorry

end ReferencePricing.Myopic
