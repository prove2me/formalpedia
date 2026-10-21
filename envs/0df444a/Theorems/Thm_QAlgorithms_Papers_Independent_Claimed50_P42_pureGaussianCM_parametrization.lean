-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P42_pureGaussianCM_parametrization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P42.pureGaussianCM_parametrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:04:04.573404+00:00
-- url     : https://prove2.me/theorems/0b822405-3082-4277-a297-47e244787f7c
-- title:
--   Parametrization of pure Gaussian covariance matrices
-- statement:
--   Let $n\ge 0$ be the number of bosonic modes, with $\hbar=1$ and covariance equal to twice the ordinary symmetrized covariance, so the vacuum covariance is the identity. Use grouped coordinates $(Q_1,\ldots,Q_n,P_1,\ldots,P_n)$ and write $\sigma_n=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$. A real symmetric $2n\times2n$ matrix $\gamma_p$ is a pure Gaussian covariance matrix (that is, $\gamma_p-i\sigma_n\succeq0$ and $\det\gamma_p=1$) if and only if there exist real symmetric $n\times n$ matrices $X,Y$, with $X\succ0$, such that
--
--   $$
--   \gamma_p=\begin{pmatrix}X&XY\\YX&YXY+X^{-1}\end{pmatrix}.
--   $$
--
--   This characterizes all pure Gaussian covariance matrices without introducing wavefunctions or truncating the bosonic Hilbert space. Positive definiteness makes the inverse genuine; empty matrices give the dimension-zero case.
-- source:
--   Gaussian Entanglement of Formation, arXiv:quant-ph/0306177v2, PDF p. 3, Lemma 1, Eq.(16)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P42

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase sigma pureCovariance)

/-- Lemma 1, PDF pp.3–4, Eq.(16). The accepted pureCovariance predicate is
real symmetry, gamma - i sigma positive semidefinite, and det gamma = 1.
Thus it uses the paper's doubled covariance and vacuum CM I, with hbar = 1.
Positive definiteness of X includes real symmetry. No wavefunction or
finite-dimensional truncation of the bosonic Hilbert space is introduced. -/
theorem pureGaussianCM_parametrization (n : ℕ)
    (gamma : Matrix (Phase n) (Phase n) ℝ) (hgamma : gamma.IsSymm) :
    pureCovariance gamma (sigma n) ↔
      ∃ X Y : Matrix (Fin n) (Fin n) ℝ,
        X.PosDef ∧ Y.IsSymm ∧ gamma = pureGaussianCM X Y := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P42

end
