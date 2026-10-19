-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_efficient_support_additive
-- name    : QAlgorithms.Papers.Independent.Information100.P27.efficient_support_additive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:17:16.966551+00:00
-- url     : https://prove2.me/theorems/32c54797-12b1-416f-8a43-6f097cbc0c31
-- title:
--   Proposition 8.4: efficient restriction is strongly additive
-- statement:
--   For $k=1,2$, let $p_k$ be a strictly positive probability distribution on a nonempty finite label set $Y_k$, and let $(e_{k,i})_{i\in Y_k}$ be normalized pure environmental density matrices on a nonempty finite system $E_k$. Such data describe the associated source of a maximally correlated state. For $\mu\ge0$, put $g_{k,\mu}(q)=H(q)-(1+\mu)H(\sum_iq_ie_{k,i})$, and let $S^{\mathrm{eff}}_\mu(p_k,e_k)$ be the supremum of $\sum_x w_xg_{k,\mu}(q_x)$ over finite probability ensembles with $\sum_xw_xq_x=p_k$. Then
--
--   $$
--   S^{\mathrm{eff}}_\mu(p_1\otimes p_2,e_1\otimes e_2)=S^{\mathrm{eff}}_\mu(p_1,e_1)+S^{\mathrm{eff}}_\mu(p_2,e_2).
--   $$
--
--   The joint conditional states are $e_{1,i}\otimes e_{2,j}$ and the input probabilities are $p_{1,i}p_{2,j}$. This is strong additivity of the efficient restriction, with no claim about unrestricted instrument support.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 37, Proposition 8.4: efficient restriction is strongly additive

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF p.37, Proposition 8.4 (proof p.70): efficient strong
additivity, retaining each source's own conditional environmental states. -/
theorem efficient_support_additive
    {Y1 Y2 E1 E2 : Type} [Fintype Y1] [Fintype Y2] [Fintype E1] [Fintype E2]
    [Nonempty Y1] [Nonempty Y2] [Nonempty E1] [Nonempty E2]
    (p1 : Y1 → ℝ) (p2 : Y2 → ℝ)
    (e1 : Y1 → Matrix E1 E1 ℂ) (e2 : Y2 → Matrix E2 E2 ℂ)
    (hp1 : IsProbability p1) (hp2 : IsProbability p2)
    (hpos1 : ∀ i, 0 < p1 i) (hpos2 : ∀ i, 0 < p2 i)
    (he1 : ∀ i, IsDensityMatrix (e1 i)) (he2 : ∀ i, IsDensityMatrix (e2 i))
    (hpure1 : IsPureFamily e1) (hpure2 : IsPureFamily e2)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    efficientSupport mu (fun i : Y1 × Y2 => p1 i.1 * p2 i.2)
      (fun i => Matrix.kronecker (e1 i.1) (e2 i.2)) =
      efficientSupport mu p1 e1 + efficientSupport mu p2 e2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
