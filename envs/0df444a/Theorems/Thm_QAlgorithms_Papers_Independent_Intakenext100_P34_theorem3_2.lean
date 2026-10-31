-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P34_theorem3_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P34.theorem3_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:05:55.097699+00:00
-- url     : https://prove2.me/theorems/afbbc29a-732a-4f17-9593-1b0cd8aeb452
-- title:
--   Canonical degenerate compression elements and their recursions
-- statement:
--   Let $C$ be a commutative unital ring in which $2$ is invertible, let $\epsilon\in\{1,-1\}$, and fix scalars $z_0^{(\ell)}\in C$ for all $\ell\ge0$. Write $\mathcal W_k$ for the actual quotient defined by (2.1)–(2.5) and (2.21)–(2.24), and $z_0(u)=\sum_{\ell\ge0}z_0^{(\ell)}u^{-\ell}$.
--
--   There is a compatible choice of polynomial representatives $z_n^{(\ell)}\in\mathcal W_n$ ($n,\ell\ge0$), starting at the supplied scalars $z_0^{(\ell)}$, such that these representatives are central and
--   $$
--   e_i y_i^\ell e_i=z_{i-1}^{(\ell)}e_i.
--   $$
--   The representatives are the coefficients of the explicit polynomial-valued series
--   $$
--   z_n(u)=(z_0(u)+\epsilon u-\tfrac12)\prod_{j=1}^n R(y_j,u)-\epsilon u+\tfrac12,
--   \qquad R(y,u)=\frac{((u+y)^2-1)(u-y)^2}{((u-y)^2-1)(u+y)^2}.
--   $$
--   For every $i\ge1$, in level $i+1$,
--   $$
--   (z_{i-1}(-u)-\tfrac12-\epsilon u)(z_{i-1}(u)-\tfrac12+\epsilon u)e_i
--   =(\tfrac12-\epsilon u)(\tfrac12+\epsilon u)e_i.
--   $$
--   In level $i+2$,
--   $$
--   (z_i(u)+\epsilon u-\tfrac12)e_{i+1}
--   =(z_{i-1}(u)+\epsilon u-\tfrac12)R(y_i,u)e_{i+1}.
--   $$
--   For $k\ge1$, in level $k+1$,
--   $$
--   (z_{k-1}(u)+\epsilon u-\tfrac12)e_k
--   =(z_0(u)+\epsilon u-\tfrac12)\prod_{j=1}^{k-1}R(y_j,u)e_k.
--   $$
--   Every representative is evaluated at a larger level using its explicit polynomial in the initial variables. No injectivity of a tower map or uniqueness of a compression representative is assumed. The level-zero representatives are scalars.
--
--   This gives central compression elements and all three source identities even for nonadmissible parameters.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, PDF p. 14, Theorem 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Theorem 3.2, PDF pp.13--14. Existence is witnessed by the explicitly
constructed coefficient polynomials; centrality, compression and all three
identities remain conclusions, with no admissibility assumption. In (3.9)
the two printed e_(i+1) are corrected to e_k, as forced by iteration of (3.8). -/
theorem theorem3_2 (P : DParams C) :
    (∀ (n ell : ℕ), 0 < n → Central (dMomentAt C P n n ell (le_refl n))) ∧
    (∀ (n ell : ℕ),
      let j : Adj (n+2) := ⟨n, by omega⟩
      let m := dwMap C P (n+2)
      m (de C j)*m (dy C (adjacentLeft j))^ell*m (de C j) =
        dMomentAt C P n (n+2) ell (by omega)*m (de C j)) ∧
    (∀ n : ℕ,
      let j : Adj (n+2) := ⟨n, by omega⟩
      let e := ps (dwMap C P (n+2) (de C j))
      let half := ps (algebraMap C (DW C P (n+2)) (↑P.two⁻¹ : C))
      let eps := ps (algebraMap C (DW C P (n+2)) P.epsilon)
      let t : PowerSeries (DW C P (n+2)) := PowerSeries.X
      (t*dMomentSeries C P n (n+2) (by omega) true-half*t-eps)*
        (t*dMomentSeries C P n (n+2) (by omega) false-half*t+eps)*e =
        (half*t-eps)*(half*t+eps)*e) ∧
    (∀ n : ℕ,
      let j : Adj (n+3) := ⟨n+1, by omega⟩
      let y : Fin (n+3) := ⟨n, by omega⟩
      let e := ps (dwMap C P (n+3) (de C j))
      let half := ps (algebraMap C (DW C P (n+3)) (↑P.two⁻¹ : C))
      let eps := ps (algebraMap C (DW C P (n+3)) P.epsilon)
      let t : PowerSeries (DW C P (n+3)) := PowerSeries.X
      (t*dMomentSeries C P (n+1) (n+3) (by omega)+eps-half*t)*e =
        (t*dMomentSeries C P n (n+3) (by omega)+eps-half*t)*
        dRatio (dwMap C P (n+3) (dy C y))*e) ∧
    (∀ (k : ℕ) (hk : 0 < k),
      let j : Adj (k+1) := ⟨k-1, by omega⟩
      let e := ps (dwMap C P (k+1) (de C j))
      let half := ps (algebraMap C (DW C P (k+1)) (↑P.two⁻¹ : C))
      let eps := ps (algebraMap C (DW C P (k+1)) P.epsilon)
      let t : PowerSeries (DW C P (k+1)) := PowerSeries.X
      (t*dMomentSeries C P (k-1) (k+1) (by omega)+eps-half*t)*e =
        (t*dMomentSeries C P 0 (k+1) (by omega)+eps-half*t)*
        dRatioProduct (fun a : Fin (k-1) => dwMap C P (k+1)
          (dy C (⟨a.val, by have := a.isLt; omega⟩ : Fin (k+1))))*e) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P34
