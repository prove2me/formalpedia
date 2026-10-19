-- Prove2me | Theorems.Thm_UnknownProphet_NoSamples_lemma_2
-- name    : UnknownProphet.NoSamples.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:42.597229+00:00
-- url     : https://prove2.me/theorems/14e5af53-042f-47fb-b1d0-57ab69a4f8fa
-- title:
--   Lemma 2, p. 8 — order-oblivious rule with the same guarantee
-- statement:
--   Let $n$ be a horizon, $\alpha$ an approximation ratio, and $r$ a zero-sample stopping rule that achieves $\alpha$ for every finitely supported nonnegative law. Then another zero-sample rule $r'$ satisfies
--
--   $$
--   \operatorname{Guarantee}(r',\alpha),\qquad r'\text{ is order oblivious},\qquad \forall i,\;r\text{ never selects }X_i\implies r'\text{ never selects }X_i.
--   $$
--
--   This reduces the rule class while preserving its distribution-uniform guarantee and positions that the original rule never selects.
--
--   **Formalization Note** Times are zero-based in Lean. “Never selects” uses zero conditional stopping probability on every nonnegative history. The guarantee quantifies over finitely supported laws.
-- source:
--   Correa, Dütting, Fischer & Schewior, Prophet Inequalities for I.I.D. Random Variables from an Unknown Distribution, arXiv:1811.06114v2, p. 8, Lemma 2

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples

/-- Lemma 2, p. 8: order-oblivious rules suffice without loss of guarantee. -/
theorem lemma_2 (n : ℕ) (α : ℝ) (R : StoppingRule 0 n)
    (hR : HasGuarantee R α) :
    ∃ R' : StoppingRule 0 n,
      HasGuarantee R' α ∧ OrderOblivious R' ∧
        ∀ i, NeverSelects R i → NeverSelects R' i := by sorry

end UnknownProphet.NoSamples
