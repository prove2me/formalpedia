-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_kl_likelihood_tail
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.kl_likelihood_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:56:11.74399+00:00
-- url     : https://prove2.me/theorems/1a64725a-14c9-4e69-b7dd-6bed6c2fb414
-- title:
--   Lemma 6: KL controls an upper likelihood tail
-- statement:
--   Let $p,q$ be probability mass functions on an arbitrary discrete set $\Omega$, and let $\alpha\in\mathbb R$ be unrestricted. Define the log likelihood as $\log(p(\omega)/q(\omega))$ on positive common support, as $+\infty$ when $p(\omega)>0=q(\omega)$, and assign any value at $p(\omega)=0$ without affecting its $p$-probability. With natural logarithms and extended nonnegative KL divergence,
--   $$
--   D(p\|q)+e^{-1}\ge\alpha\,p\!\left\{\log\frac{p(\omega)}{q(\omega)}\ge\alpha\right\}.
--   $$
--   No finiteness or absolute-continuity condition is imposed. For $\alpha\le0$ the right side is nonpositive; for $\alpha>0$ the formula is a likelihood-tail estimate useful for the normalized-KL converse.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 9, Lemma 6, (35): KL controls an upper likelihood tail

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF pp.9–10, Lemma 6, (35): alpha is ANY real. No finite-alphabet
or absolute-continuity assumption; support mismatches remain infinite. -/
theorem kl_likelihood_tail {Omega : Type*} (p q : PMF Omega) (alpha : ℝ) :
    ((alpha * (∑' w, if (alpha : EReal) ≤ logLikelihood (p w) (q w)
      then p w else 0).toReal : ℝ) : EReal) ≤
      (discreteKLDivergence p q : EReal) + ((1 / Real.exp 1 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
