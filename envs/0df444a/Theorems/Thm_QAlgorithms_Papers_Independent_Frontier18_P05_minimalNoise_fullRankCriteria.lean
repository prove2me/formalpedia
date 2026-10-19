-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_minimalNoise_fullRankCriteria
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.minimalNoise_fullRankCriteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:48:38.899011+00:00
-- url     : https://prove2.me/theorems/fe6477b0-947a-4d12-9822-c45b4d5a7f21
-- title:
--   Equivalent full-rank minimal-noise criteria
-- statement:
--   Let $n\ge1$, $X,Y\in\mathbb R^{2n\times2n}$, and $\Sigma=\sigma_n-X^T\sigma_nX$, with $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. Suppose $Y-i\Sigma\succeq0$ and $\operatorname{rank}Y=\operatorname{rank}\Sigma=2n$. Say that $Y$ is minimal at fixed $X$ if every CP noise $Z\preceq Y$ equals $Y$. Write $Y^+$ for its support inverse, $r=\operatorname{rank}\Sigma$, and $r'=\operatorname{rank}Y-\operatorname{rank}(Y-\Sigma Y^+\Sigma^T)$. Then minimality is equivalent to each of
--
--   $$Y=\Sigma Y^{-1}\Sigma^T,\qquad \det Y=\det\Sigma,\qquad r=r'.$$
--
--   These tests characterize minimal noise in the full-rank regime. All ranks are real, and the difference defining $r'$ is an integer difference.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 17, §2.3: Equivalent full-rank minimal-noise criteria (m1)–(m3)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Section 2.3, PDF p.17, Eqs.(66)–(68): all three class-(i) tests.
Full rank guards the ordinary inverse and determinant test. The rank subtraction
in rprime is integer subtraction, not truncated natural subtraction. -/
theorem minimalNoise_fullRankCriteria {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef)
    (hY : Y.rank = 2 * n) (hSigma : (commutatorDefect X).rank = 2 * n) :
    (minimalNoise X Y ↔
      Y = commutatorDefect X * Y⁻¹ * (commutatorDefect X).transpose) ∧
    (minimalNoise X Y ↔ Y.det = (commutatorDefect X).det) ∧
    (minimalNoise X Y ↔
      ((commutatorDefect X).rank : ℤ) =
        (Y.rank : ℤ) - ((rankResidual Y (commutatorDefect X)).rank : ℤ)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end
