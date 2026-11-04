-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_finiteEntropy_mul_conjTranspose_eq_transpose
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.finiteEntropy_mul_conjTranspose_eq_transpose
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-03T22:43:46.362512+00:00
-- url     : https://prove2.me/theorems/7c9ed0ed-e90d-483b-a98f-294b2c5d8381
-- title:
--   The two reduced operators of a finite bipartite vector have equal homogeneous entropy
-- statement:
--   Throughout, for a finite index type $n$ and $X\in M_n(\mathbb C)$, $H(X)$ denotes the frozen `finiteEntropy` of Frontier18.P01, the homogeneous entropy $H(X)=\max\bigl(0,\,-\operatorname{Tr}\eta(X)+\operatorname{Tr}X\,\log\operatorname{Tr}X\bigr)\in[0,\infty)$ with $\eta(x)=x\log x$ applied by the continuous functional calculus (natural logarithms, $0\log 0=0$). For a positive semidefinite $X\ne0$ this is $\operatorname{Tr}X\cdot S(X/\operatorname{Tr}X)$, with $S$ the von Neumann entropy, and $H(0)=0$. Let $m,n$ be finite index types and $W\in M_{m\times n}(\mathbb C)$, viewed as the (unnormalized) pure bipartite vector $\sum_{i,r}W_{ir}\,e_i\otimes f_r$. Its two reduced operators are $WW^*\in M_m$ and $W^{\mathsf T}(W^{\mathsf T})^*=\overline{W^*W}\in M_n$. Then
--
--   $$
--   H(WW^*)=Higl(W^{\mathsf T}(W^{\mathsf T})^*igr).
--   $$
--
--   This is the finite-dimensional Schmidt fact: $WW^*$ and $W^*W$ have the same nonzero eigenvalues with multiplicities, entrywise conjugation preserves the spectrum of a Hermitian matrix, and $\eta(0)=0$.
-- source:
--   Kuznetsova, Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1 (step H(AB)=H(C) for pure rho_ABC); Lindblad, Commun. Math. Phys. 39 (1974) 111-119 (homogeneous entropy, Lemma 1 compression limit); Wehrl, Rev. Mod. Phys. 50 (1978) 221, §II.B (concavity, continuity of entropy in finite dimensions)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

open scoped Matrix ComplexOrder

theorem finiteEntropy_mul_conjTranspose_eq_transpose {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (W : Matrix m n ℂ) :
    finiteEntropy (W * Wᴴ) = finiteEntropy (Wᵀ * Wᵀᴴ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
