-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_simplexBellForm
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.simplexBellForm
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:46:23.22959+00:00
-- url     : https://prove2.me/theorems/82bed5e4-8226-4295-9bb6-80068217681f
-- title:
--   IV A: Bell-diagonal structure of same-code simplex postselection, (21)–(22)
-- statement:
--   Let $C=(C_k)_{k=0}^{m-1}$ be distinct binary words of length $n\ge1$, with $m\ge2$, such that every pair of distinct words has Hamming distance $d$, where $1\le d\le n$. For $0\le Q\le\tfrac12$, let $P$ be the operator after both parties filter the six-state input on $C$. Put $s=((1-Q)/2)^n$, $u=Q^d(1-Q)^{n-d}/2^n$, $v=(1-2Q)^d(1-Q)^{n-d}/2^n$, and $Z=ms+m(m-1)u$. Then $\operatorname{Tr}P=Z>0$. For the orthonormal Bell basis $|\Phi_{kl}\rangle=(I\otimes X^kZ^l)m^{-1/2}\sum_j|j,j\rangle$, using cyclic shift and positive clock phase,
--
--   $$\frac{P}{Z}=\sum_{k,l}x_{kl}|\Phi_{kl}\rangle\langle\Phi_{kl}|,
--   \quad x_{00}=a=\frac{s+(m-1)v}{Z},\quad
--   x_{0l}=b=\frac{s-v}{Z}\ (l\ne0),\quad
--   x_{kl}=\frac{u}{Z}=\frac{1-a-(m-1)b}{m(m-1)}\ (k\ne0).$$
--
--   These are actual eigenvalues, with $a\ge b\ge0$ and $a+(m-1)b\le1$. Thus there are at most three eigenvalues, with degeneracy allowed. Normalization is explicit, and the coefficients are constructed from the code parameters rather than supplied as free hypotheses.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 8, IV A: Bell-diagonal structure of same-code simplex postselection, (21)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.8, (21)–(22): the normalized, constructed same-code simplex operator
is Bell diagonal, with the three explicitly computed spectral sectors. -/
theorem simplexBellForm {n m d : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hd0 : 1 ≤ d) (hdn : d ≤ n) (C : Fin m → Qubits n)
    (hC : Function.Injective C) (hd : Equidistant C d)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1 / 2) :
    0 < simplexZ n m d Q ∧
    (bothState C Q).trace = (simplexZ n m d Q : ℂ) ∧
    IsDensityMatrix (((simplexZ n m d Q)⁻¹ : ℂ) • bothState C Q) ∧
    (((simplexZ n m d Q)⁻¹ : ℂ) • bothState C Q =
      ∑ k : Fin m, ∑ l : Fin m,
        (simplexWeights n m d Q k l : ℂ) • pureDensity (cyclicBellVector m k l)) ∧
    (∀ k l k2 l2 : Fin m,
      inner ℂ (cyclicBellVector m k l) (cyclicBellVector m k2 l2) =
        if k = k2 ∧ l = l2 then 1 else 0) ∧
    (∀ k l : Fin m, act (((simplexZ n m d Q)⁻¹ : ℂ) • bothState C Q) (cyclicBellVector m k l) =
      (simplexWeights n m d Q k l : ℂ) • cyclicBellVector m k l) ∧
    0 ≤ simplexB n m d Q ∧ simplexB n m d Q ≤ simplexA n m d Q ∧
    simplexA n m d Q + (m - 1) * simplexB n m d Q ≤ 1 ∧
    (∀ k l : Fin m, k.val ≠ 0 →
      simplexWeights n m d Q k l =
        (1 - simplexA n m d Q - (m - 1) * simplexB n m d Q) / (m * (m - 1))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
