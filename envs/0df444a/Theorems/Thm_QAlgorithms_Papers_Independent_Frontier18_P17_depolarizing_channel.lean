-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_depolarizing_channel
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.depolarizing_channel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:35:36.465879+00:00
-- url     : https://prove2.me/theorems/75953ecc-05a1-41dc-8bd0-f8b8c3436657
-- title:
--   Depolarizing channel and the valid Pauli Kraus family
-- statement:
--   Let $0\le p\le1$. For every integer $N\ge1$, the map $\Delta_{N,p}(X)=pX+(1-p)I_N\operatorname{tr}(X)/N$ is a quantum channel. For a qubit, let $\sigma_x,\sigma_y,\sigma_z$ be the usual Pauli matrices and put
--
--   $$K_0=\frac{\sqrt{1+3p}}2I_2,\qquad (K_1,K_2,K_3)=\frac{\sqrt{1-p}}2(\sigma_x,\sigma_y,\sigma_z).$$
--
--   These operators satisfy $\sum_{i=0}^3K_i^\dagger K_i=I_2$ and $\Delta_{2,p}(\rho)=\sum_{i=0}^3K_i\rho K_i^\dagger$ for every density matrix $\rho$. In particular, for real $a,b,c$ such that $\rho=\begin{pmatrix}a&b+ic\\b-ic&1-a\end{pmatrix}$ is a density matrix,
--
--   $$\Delta_{2,p}(\rho)=\begin{pmatrix}\tfrac12+(a-\tfrac12)p&(b+ic)p\\(b-ic)p&\tfrac12-(a-\tfrac12)p\end{pmatrix},\qquad
--   D_{\Delta_{2,p}}=\begin{pmatrix}(1+p)/2&0&0&p\\0&(1-p)/2&0&0\\0&0&(1-p)/2&0\\p&0&0&(1+p)/2\end{pmatrix}.$$
--
--   This retains the parameter convention $p=1$ for identity and $p=0$ for complete depolarization. It uses the valid family in Eq. (57), not the conflicting printed singular system in Eqs. (54)–(56).
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 7, Example 4, Eqs.(50)–(53),(57)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.7, Example 4, Eqs. (50)–(53),(57): depolarizing channel and its valid
Pauli Kraus family. The frozen general channel takes noise weight 1-p, while
the frozen qubit map takes signal weight p. The incompatible Eqs. (54)–(56)
are deferred separately. -/
theorem depolarizing_channel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ (N : ℕ) (hN : 0 < N),
      QAlgorithms.IsChannel (QAlgorithms.QuditFidelity.depolarizingMap N hN (1-p))) ∧
    QAlgorithms.IsKrausFamily (depolarizingKraus p) ∧
    (∀ rho : Matrix Bool Bool ℂ, QAlgorithms.IsDensityMatrix rho →
      depolarizing p rho = QAlgorithms.krausApply (depolarizingKraus p) rho) ∧
    (∀ a b c : ℝ, let rho : Matrix Bool Bool ℂ := fun i j =>
        if i then (if j then ((1-a : ℝ) : ℂ) else (b : ℂ)-Complex.I*c)
        else (if j then (b : ℂ)+Complex.I*c else (a : ℂ));
      QAlgorithms.IsDensityMatrix rho →
      depolarizing p rho = (fun i j =>
        if i then (if j then ((1/2 - (a-1/2)*p : ℝ) : ℂ) else ((b : ℂ)-Complex.I*c)*p)
        else (if j then ((b : ℂ)+Complex.I*c)*p else ((1/2 + (a-1/2)*p : ℝ) : ℂ)))) ∧
    dynamical (depolarizing p) = (fun x y =>
      if x = y then (if x.1 = x.2 then ((1+p : ℝ) : ℂ)/2 else ((1-p : ℝ) : ℂ)/2)
      else if x.1 = x.2 ∧ y.1 = y.2 then (p : ℂ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
