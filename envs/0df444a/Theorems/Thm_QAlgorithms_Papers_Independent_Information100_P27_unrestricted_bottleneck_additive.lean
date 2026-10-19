-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_unrestricted_bottleneck_additive
-- name    : QAlgorithms.Papers.Independent.Information100.P27.unrestricted_bottleneck_additive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:17:56.954727+00:00
-- url     : https://prove2.me/theorems/8834ce98-0a32-4057-88c3-689050279a0d
-- title:
--   Theorem 8.8: unrestricted bottleneck strong additivity
-- statement:
--   Let $\omega_k=\sum_{i\in Y_k}p_{k,i}|i\rangle\langle i|\otimes e_{k,i}$, for $k=1,2$, be finite classical–quantum sources. Each $p_k$ is a probability distribution and every $e_{k,i}$ is a density matrix; the conditional states may be mixed. For $\alpha\ge0$, let $J_\alpha(\omega_k)$ be the supremum of $\alpha I(T;E_k)-I(T;Y_k)$ over all density families $\tau_i$ on arbitrary finite memories, evaluated on $\sum_i p_{k,i}|i\rangle\langle i|\otimes\tau_i\otimes e_{k,i}$. Then
--
--   $$
--   J_\alpha(\omega_1\otimes\omega_2)=J_\alpha(\omega_1)+J_\alpha(\omega_2).
--   $$
--
--   The product source has independent label probabilities, while its optimized memory can depend jointly on both labels. No uniform memory dimension bound is imposed. This is the unrestricted additivity result, separate from the flagged-pure memory conjecture.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 40, Theorem 8.8: unrestricted bottleneck strong additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF p.40, Theorem 8.8 (proof pp.75-76): unrestricted
bottleneck additivity for arbitrary mixed classical-quantum sources. -/
theorem unrestricted_bottleneck_additive
    {Y1 Y2 E1 E2 : Type} [Fintype Y1] [Fintype Y2] [Fintype E1] [Fintype E2]
    [Nonempty Y1] [Nonempty Y2] [Nonempty E1] [Nonempty E2]
    (p1 : Y1 → ℝ) (p2 : Y2 → ℝ)
    (e1 : Y1 → Matrix E1 E1 ℂ) (e2 : Y2 → Matrix E2 E2 ℂ)
    (hp1 : IsProbability p1) (hp2 : IsProbability p2)
    (he1 : ∀ i, IsDensityMatrix (e1 i)) (he2 : ∀ i, IsDensityMatrix (e2 i))
    (alpha : ℝ) (halpha : 0 ≤ alpha) :
    bottleneck alpha (fun i : Y1 × Y2 => p1 i.1 * p2 i.2)
      (fun i => Matrix.kronecker (e1 i.1) (e2 i.2)) =
      bottleneck alpha p1 e1 + bottleneck alpha p2 e2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
