-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_2_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_2_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:57:42.690763+00:00
-- url     : https://prove2.me/theorems/6b72b82b-1a24-4cf9-b939-be463a6abba5
-- title:
--   Six integer-power commutation identities
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed.
--
--   Let $1\le k<n$ and $a\ge1$ be integers, and write $T_k^{-1}=T_k-\delta+\delta E_k$. All six identities hold:
--   $$\begin{aligned}
--   T_kX_k^a&=X_{k+1}^aT_k+\sum_{i=1}^a\delta X_{k+1}^{i}(E_k-1)X_k^{a-i},\\
--   T_k^{-1}X_k^a&=X_{k+1}^aT_k^{-1}+\sum_{i=1}^a\delta X_{k+1}^{a-i}(E_k-1)X_k^i,\\
--   E_kX_k^aT_k&=\rho E_kX_k^{-a}+\delta\sum_{i=1}^a E_kX_k^{a-i}E_kX_k^{-i}-\delta\sum_{i=1}^a E_kX_k^{a-2i},\\
--   T_kX_k^{-a}&=X_{k+1}^{-a}T_k-\sum_{i=1}^a\delta X_{k+1}^{-a+i}(E_k-1)X_k^{-i},\\
--   T_k^{-1}X_k^{-a}&=X_{k+1}^{-a}T_k^{-1}-\sum_{i=1}^a\delta X_{k+1}^{-i}(E_k-1)X_k^{-a+i},\\
--   E_kX_k^{-a}T_k&=\rho E_kX_k^a-\delta\sum_{i=1}^a E_kX_k^{-i}E_kX_k^{a-i}+\delta\sum_{i=1}^a E_kX_k^{a-2i}.
--   \end{aligned}$$
--
--   These are the positive- and negative-power relations used to move generators through Laurent monomials.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 3, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section Presentation

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

local notation "t" => ruiXuFreeT R n

local notation "e" => ruiXuFreeE R n

local notation "x" => ruiXuFreeX R n

local notation "c" => algebraMap R (FreeAlgebra R (RuiXuLetter n))

/-- Lemma 2.3, PDF p.3: all six identities. Exponents are integers,
including a-2i and -a+i; a and k are positive. -/
theorem lemma_2_3 (k a : ℕ) (hk : 1 ≤ k ∧ k < n) (ha : 1 ≤ a) :
    let scalarMap := algebraMap R (RuiXuBMW P n)
    let d := scalarMap (P.delta : R)
    let h := scalarMap (P.rho : R)
    (T P n k * XPow P n k (a : ℤ) = XPow P n (k+1) (a : ℤ) * T P n k +
      ∑ i ∈ Finset.Icc 1 a, d * XPow P n (k+1) (i : ℤ) * (ruiXuE P n k - 1) *
        XPow P n k ((a : ℤ) - i)) ∧
    (TInv P n k * XPow P n k (a : ℤ) = XPow P n (k+1) (a : ℤ) * TInv P n k +
      ∑ i ∈ Finset.Icc 1 a, d * XPow P n (k+1) ((a : ℤ) - i) * (ruiXuE P n k - 1) *
        XPow P n k (i : ℤ)) ∧
    (ruiXuE P n k * XPow P n k (a : ℤ) * T P n k = h * ruiXuE P n k * XPow P n k (-(a : ℤ)) +
      d * (∑ i ∈ Finset.Icc 1 a, ruiXuE P n k * XPow P n k ((a : ℤ) - i) *
        ruiXuE P n k * XPow P n k (-(i : ℤ))) -
      d * (∑ i ∈ Finset.Icc 1 a, ruiXuE P n k * XPow P n k ((a : ℤ) - 2 * i))) ∧
    (T P n k * XPow P n k (-(a : ℤ)) = XPow P n (k+1) (-(a : ℤ)) * T P n k -
      ∑ i ∈ Finset.Icc 1 a, d * XPow P n (k+1) (-(a : ℤ) + i) * (ruiXuE P n k - 1) *
        XPow P n k (-(i : ℤ))) ∧
    (TInv P n k * XPow P n k (-(a : ℤ)) = XPow P n (k+1) (-(a : ℤ)) * TInv P n k -
      ∑ i ∈ Finset.Icc 1 a, d * XPow P n (k+1) (-(i : ℤ)) * (ruiXuE P n k - 1) *
        XPow P n k (-(a : ℤ) + i)) ∧
    (ruiXuE P n k * XPow P n k (-(a : ℤ)) * T P n k = h * ruiXuE P n k * XPow P n k (a : ℤ) -
      d * (∑ i ∈ Finset.Icc 1 a, ruiXuE P n k * XPow P n k (-(i : ℤ)) *
        ruiXuE P n k * XPow P n k ((a : ℤ) - i)) +
      d * (∑ i ∈ Finset.Icc 1 a, ruiXuE P n k * XPow P n k ((a : ℤ) - 2 * i))) := by sorry

end Presentation

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
