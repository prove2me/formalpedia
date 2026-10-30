-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_smoothMaxPenalty
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.smoothMaxPenalty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:23:09.631713+00:00
-- url     : https://prove2.me/theorems/882e6616-79e3-4ea2-a0eb-0aa626cf0d19
-- title:
--   Smooth-max correlation penalty exceeds minus one
-- statement:
--   Let $p_{UV}$ be any normalized joint law on finite alphabets, and let $0\le\varepsilon\le1/2$. For each set $G\subseteq U\times V$ of mass $p_{UV}(G)>1-\varepsilon$, take the maximum over $G$ of $\log_2[p_{UV}(u,v)/(p_U(u)p_V(v))]$, keeping the original marginals. Let $I_\infty^\varepsilon(U;V)$ be the extended infimum of these maxima. Zero joint mass has log likelihood ratio $-\infty$; the empty feasible family at $\varepsilon=0$ has infimum $+\infty$. Then
--   $$I_\infty^\varepsilon(U;V)>-1.$$
--   The endpoint $\varepsilon=1/2$ is included. In particular, the sum-rate penalty $5+I_\infty^{\varepsilon_\infty}(U;V)$ in Remark 1 is positive for $\varepsilon_\infty\le1/4$.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 5, Remark 3; Remark 1 specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 3, PDF p.5, with Remark 1, PDF p.4. The interval is CLOSED at 1/2;
epsilon=0 gives +infinity in the strict smoothing convention. -/
theorem smoothMaxPenalty {U V : Type} [Fintype U] [Fintype V]
    (p : AuxiliaryLaw (U × V)) (epsilon : ℝ) (hEpsilon : 0 ≤ epsilon ∧ epsilon ≤ 1 / 2) :
    (-1 : EReal) < strictSmoothMaxInformation p.prob epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end
