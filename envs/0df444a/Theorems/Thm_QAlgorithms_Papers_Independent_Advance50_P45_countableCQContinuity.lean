-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P45_countableCQContinuity
-- name    : QAlgorithms.Papers.Independent.Advance50.P45.countableCQContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:20:25.811704+00:00
-- url     : https://prove2.me/theorems/090f6ace-4f76-40f0-9a54-c1df5da3bb2e
-- title:
--   CQ conditional-entropy continuity for countable classical conditioning
-- statement:
--   Let $\mathcal X$ be a countable alphabet, including the finite case, and let $B$ be a nonzero finite-dimensional quantum system of dimension $d_B$. Let $r,s$ be probability distributions on $\mathcal X$ and let $\rho_B^x,\sigma_B^x$ be normalized density operators for every $x$. In the same classical basis form the direct-sum states
--   $$
--   \rho_{XB}=\bigoplus_x r(x)\rho_B^x,
--   \qquad \sigma_{XB}=\bigoplus_x s(x)\sigma_B^x.
--   $$
--   Define $H(B|X)_\rho=\sum_x r(x)H(\rho_B^x)$ and analogously for $\sigma$, where $H$ is von Neumann entropy in bits. These averages converge absolutely, irrespective of whether the Shannon entropies of $r,s$ are finite. If $0<\varepsilon\le1-1/d_B$ and
--   $$
--   \tfrac12\|\rho_{XB}-\sigma_{XB}\|_1
--   =\tfrac12\sum_x\bigl\|r(x)\rho_B^x-s(x)\sigma_B^x\bigr\|_1
--   \le\varepsilon,
--   $$
--   then
--   $$
--   \bigl|H(B|X)_\rho-H(B|X)_\sigma\bigr|
--   \le\varepsilon\log_2(d_B-1)+h_2(\varepsilon).
--   $$
--   Here $\|\cdot\|_1$ is the Schatten trace norm and $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with $0\log_2 0=0$.
--
--   This extends the finite-alphabet continuity estimate to countable classical conditioning without an assumption on the entropy of the conditioning system.
-- source:
--   Optimal uniform continuity bound for conditional entropy of classical--quantum states, arXiv:1909.01755v2, PDF p. 5, Corollary 3, Eqs. (29)–(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P45

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (cqBlock)

/-- Corollary 3, PDF p.5, Eqs.(29)–(32), proof pp.6–8: the same continuity
bound for a countable common classical basis and finite quantum output B.
Conditional entropy is the convergent average of branch entropies, never a
difference of possibly infinite joint and classical entropies. -/
theorem countableCQContinuity {X B : Type*} [Countable X] [Fintype B]
    [Nonempty B] [DecidableEq B] (R S : CQState X B)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hupper : epsilon ≤ 1 - 1 / (Fintype.card B : ℝ))
    (hdistance : countableCQDistance R S ≤ epsilon) :
    |cqConditionalEntropy R - cqConditionalEntropy S| ≤
      epsilon * Real.logb 2 ((Fintype.card B : ℝ) - 1) + binEntropy2 epsilon := by sorry

end QAlgorithms.Papers.Independent.Advance50.P45

end
