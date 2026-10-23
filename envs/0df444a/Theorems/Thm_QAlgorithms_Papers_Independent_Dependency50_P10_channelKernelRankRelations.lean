-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P10_channelKernelRankRelations
-- name    : QAlgorithms.Papers.Independent.Dependency50.P10.channelKernelRankRelations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:06:30.309406+00:00
-- url     : https://prove2.me/theorems/519de001-d7cd-4337-9c5c-ef097a65955e
-- title:
--   Complex kernel and rank relations for Gaussian channel data
-- statement:
--   Let $n$ be the number of bosonic modes, use quadrature order $(Q_1,\ldots,Q_n;P_1,\ldots,P_n)$ and $\hbar=1$, and put $\sigma=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. Let $X,Y$ be arbitrary real $2n\times2n$ matrices satisfying $K:=Y-i\Sigma\succeq0$, where $\Sigma=\sigma-X^T\sigma X$. All kernels and ranks below are over $\mathbb C$. Write $Y^+$ for the Moore–Penrose inverse and $R=Y-\Sigma Y^+\Sigma^T$. Then
--
--   $$
--   \ker\Sigma\cap\ker K\subseteq\ker Y\subseteq\ker K,\qquad
--   \ker Y\subseteq\ker\Sigma,\qquad
--   \ker Y=\ker\Sigma\cap\ker K,
--   $$
--   $$
--   2\operatorname{rank}K=\operatorname{rank}Y+\operatorname{rank}R,\qquad
--   \operatorname{rank}Y\ge\operatorname{rank}\Sigma\ge
--   \operatorname{rank}Y-\operatorname{rank}R\ge0.
--   $$
--
--   These relations apply to singular noise matrices as well as nonsingular ones and identify the algebraic mode-count parameters.
-- source:
--   The optimal unitary dilation for bosonic Gaussian channels, arXiv:1009.1108v1, PDF p. 2, Section II, Eqs.(6)–(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P10

/-- Section II, PDF p.2, Eqs.(6)–(10): complex kernel relations, rank identity,
and the full inequality chain. Complete positivity enforces symmetry and
positivity of `Y`. No invertibility premise. Integer differences avoid
truncated rank subtraction. -/
theorem channelKernelRankRelations {n : ℕ}
    (X Y : Matrix (Phase n) (Phase n) ℝ)
    (hCP : (cpMatrix X Y).PosSemidef) :
    (complexKernel (complexify (commutatorDefect X)) ⊓ complexKernel (cpMatrix X Y) ≤
      complexKernel (complexify Y)) ∧
    (complexKernel (complexify Y) ≤ complexKernel (cpMatrix X Y)) ∧
    (complexKernel (complexify Y) ≤ complexKernel (complexify (commutatorDefect X))) ∧
    (complexKernel (complexify Y) =
      complexKernel (complexify (commutatorDefect X)) ⊓ complexKernel (cpMatrix X Y)) ∧
    (2 * (cpMatrix X Y).rank = (complexify Y).rank +
      (complexify (rankResidual Y (commutatorDefect X))).rank) ∧
    ((complexify (commutatorDefect X)).rank ≤ (complexify Y).rank) ∧
    (((complexify Y).rank : ℤ) -
      ((complexify (rankResidual Y (commutatorDefect X))).rank : ℤ) ≤
      ((complexify (commutatorDefect X)).rank : ℤ)) ∧
    (0 ≤ ((complexify Y).rank : ℤ) -
      ((complexify (rankResidual Y (commutatorDefect X))).rank : ℤ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P10

end
