-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_binaryLinearHierarchy
-- name    : QAlgorithms.Papers.Independent.Information100.P39.binaryLinearHierarchy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:15:56.679448+00:00
-- url     : https://prove2.me/theorems/b158b1e4-b9f9-45ec-80a9-377609ed8090
-- title:
--   Theorem 1 (Binary-linear Rényi hierarchy)
-- statement:
--   Let $b\in\mathbb F_2^M$ have independent coordinates $b_a\sim\operatorname{Bern}(p_a)$ with $0\le p_a\le1$, and let $K_T\subseteq K_C$ be linear subspaces. Set $T=b+K_T$, $C=b+K_C$, and $\Delta_r=H_r(T)-H_r(C)$, using natural logarithms and min-entropy at infinity. Then
--
--   $$\Delta_s\le\Delta_r\qquad(1\le r\le s\le\infty),$$
--
--   with finite orders restricted to integers. Empty fault families and equal kernels are allowed. This is the finite binary-linear entropy hierarchy underlying the quantum and detector applications.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 2, Theorem 1 (Binary-linear Rényi hierarchy)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Theorem 1, PDF p.2, Eq.(3), including arbitrary Bernoulli endpoints and infinity. -/
theorem binaryLinearHierarchy {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (KT KC : Submodule F2 (Bits m)) (hK : KT ≤ KC) :
    DecreasingOrders (linearDeficit p KT KC) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
