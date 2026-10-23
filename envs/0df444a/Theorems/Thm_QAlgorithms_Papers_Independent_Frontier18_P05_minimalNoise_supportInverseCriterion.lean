-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_minimalNoise_supportInverseCriterion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.minimalNoise_supportInverseCriterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:49:15.37103+00:00
-- url     : https://prove2.me/theorems/416e369e-a57c-4479-b5e4-7d8d5a4fc8d5
-- title:
--   Minimal noise characterized by the support inverse
-- statement:
--   Let $n\ge1$, $X,Y\in\mathbb R^{2n\times2n}$, and $\Sigma=\sigma_n-X^T\sigma_nX$, with $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. Assume $Y-i\Sigma\succeq0$. Let $P$ be the orthogonal projector onto the real range of $Y$ and define $Y^+=P(Y+I-P)^{-1}P$. Minimality means that every CP noise $Z$ with $Z\preceq Y$ equals $Y$. Then
--
--   $$Y\text{ is minimal at fixed }X\quad\Longleftrightarrow\quad Y=\Sigma Y^+\Sigma^T.$$
--
--   This extends the minimal-noise criterion to singular noise, including $Y=\Sigma=0$, without assigning an ordinary inverse to a singular matrix.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 17, Theorem 3: Minimal noise condition

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Theorem 3, PDF p.17, Eq.(69). The inverse is the support inverse of p.15,
Eq.(60), including zero noise. No full-rank premise is imposed. The proof's
unscaled SS^T intermediate formula is not used to define minimality. -/
theorem minimalNoise_supportInverseCriterion {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    minimalNoise X Y ↔
      Y = commutatorDefect X * supportInverse Y * (commutatorDefect X).transpose := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end
