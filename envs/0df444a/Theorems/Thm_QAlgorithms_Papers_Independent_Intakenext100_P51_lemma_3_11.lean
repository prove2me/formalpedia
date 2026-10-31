-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_3_11
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_3_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:59:40.010048+00:00
-- url     : https://prove2.me/theorems/2b4fe3f7-f782-408e-bb84-0fea68947ba2
-- title:
--   Integral moment formulas for both signs
-- statement:
--   Let $R$ be an integral domain with units $q,\delta=q-q^{-1},\rho,u_1,\ldots,u_r$, where $r\ge1$, and let $F$ be its fraction field. Assume that the $u_i$ are pairwise distinct and $u_iu_j\ne1$ for every pair, including $i=j$. Put $U=\prod_i u_i$, $\gamma_r(z)=1$ for odd $r$ and $\gamma_r(z)=-z$ for even $r$, and define
--   $$\Gamma_i=\left(\gamma_r(u_i)+\delta^{-1}\rho(u_i^2-1)\prod_{j\ne i}u_j\right)\prod_{j\ne i}\frac{u_iu_j-1}{u_i-u_j}.$$
--   The rho choice means $\rho^{-1}\in\{U,-U\}$ for odd $r$, and $\rho^{-1}\in\{q^{-1}U,-qU\}$ for even $r$. Define $\omega_a=\sum_i u_i^a\Gamma_i$ in $F$ for every $a\in\mathbb Z$.
--
--   Let $\chi(k)=1$ for even $k$ and $0$ otherwise. Define $Q_a(u)$ and $Q'_a(u)$ by
--   $$\prod_i\frac{u_i-t}{1-u_it}=\sum_{a\ge0}Q_a(u)t^a,\qquad Q'_a(u)=Q_a(u_1^{-1},\ldots,u_r^{-1}).$$
--   Set $A_a=\chi(a)+\delta^{-1}\rho UQ_a(u)$ and $B_a=\chi(a)-\delta^{-1}\rho UQ'_a(u)$. For $a\ge0$ and, respectively, $a>0$,
--   $$\omega_a=\begin{cases}A_a+\sum_{k=0}^{a-1}\chi(k)Q_{a-1-k}(u)-\delta^{-1}\rho\,\mathbf1_{a=0},&r\text{ odd},\\A_a-\sum_{k=0}^{a}\chi(k)Q_{a-k}(u)-\delta^{-1}\rho\,\mathbf1_{a=0},&r\text{ even},\end{cases}$$
--   $$\omega_{-a}=\begin{cases}B_a+\sum_{k=0}^{a-1}\chi(k)Q'_{a-1-k}(u),&r\text{ odd},\\B_a-\sum_{k=0}^{a-2}\chi(k)Q'_{a-2-k}(u),&r\text{ even}.\end{cases}$$
--   In particular every $\omega_a$ belongs to the image of $R$ in $F$. Empty sums are zero; thus the last sum is empty when $a=1$.
--
--   These formulas give integral moments without requiring division by $2$ in the coefficient ring.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 10, Lemma 3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section SpectralMoments

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Lemma 3.11, PDF p.10: both parity formulas and integrality of every
integer moment. Distinctness excludes only unequal indices; nonreciprocity
includes equal indices. No invertibility of 2 is imposed. -/
theorem lemma_3_11 [IsDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (P : RuiXuUnitParameters R r) (hrho : RhoChoice P)
    (hd : Function.Injective (fun i => (P.u i : R)))
    (hnr : ∀ i j, (P.u i : R) * (P.u j : R) ≠ 1) :
    (∀ a : ℕ, spectralMoment (K := K) P (a : ℤ) = algebraMap R K (positiveMoment P a)) ∧
    (∀ a : ℕ, 0 < a → spectralMoment (K := K) P (-(a : ℤ)) =
      algebraMap R K (negativeMoment P a)) ∧
    (∀ a : ℤ, ∃ w : R, algebraMap R K w = spectralMoment (K := K) P a) := by sorry

end SpectralMoments

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
