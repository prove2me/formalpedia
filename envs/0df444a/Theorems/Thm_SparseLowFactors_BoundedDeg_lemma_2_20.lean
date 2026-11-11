-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_2_20
-- name    : SparseLowFactors.BoundedDeg.lemma_2_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:31.809198+00:00
-- url     : https://prove2.me/theorems/b08dcc7a-1047-4fdc-83c2-23e1128e8228
-- title:
--   Lemma 2.20 — $\mathrm{Syl}_Y(\bar f,\bar f')$ for $\bar f=f(X,Y\cdot g)$ by diagonal scalings
-- statement:
--   Let $f(X,Y)\in F[X,Y]$ with $\deg_Yf=k$, let $g\in F(X)$ be non-zero, and set $\bar f(X,Y)=f(X,Y\cdot g(X))$. Viewing both as polynomials in $Y$ over $F(X)$,
--   $$\mathrm{Syl}_Y(\bar f,\bar f')=\mathrm{Diag}\big(1/g,1/g^2,\dots,1/g^{2k-1}\big)\cdot\mathrm{Syl}_Y(f,f')\cdot\mathrm{Diag}\big(g^{k+1},\dots,g^{2k-1},g^{k+1},\dots,g^{2k}\big).$$
--
--   This lets a rank-preserving point be found from the Sylvester matrix of the sparse $f$ instead of its normalization (Lemma 3.2).
--
--   **Formalization Note** Both Sylvester matrices have the explicit sizes $k$ and $k-1$ (for $f'$), as in the proof; $\mathrm{Diag}$ has $2k-1$ entries, the right one listing $g^{k+1},\dots,g^{2k-1}$ for the first $k-1$ columns and $g^{k+1},\dots,g^{2k}$ for the last $k$. Derivatives are in $Y$. $F(X)$ is the fraction field of $F[X_1,\dots,X_n]$.
--
--   Differences from the source:
--   - encoding: Syl_Y(f̄, f̄′) with sizes deg f̄, deg f̄′ → explicit sizes k and k − 1; reason: the proof states deg_Y f′ = k − 1; with natDegree sizes the matrices change size when char F divides k
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 21, Lemma 2.20

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem lemma_2_20 (F : Type) [Field F] (n k : ℕ) (f : Polynomial (MvPolynomial (Fin n) F))
    (hk : f.natDegree = k) (g : FractionRing (MvPolynomial (Fin n) F)) (hg : g ≠ 0) :
    let fK : Polynomial (FractionRing (MvPolynomial (Fin n) F)) :=
      f.map (algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)))
    let fbar : Polynomial (FractionRing (MvPolynomial (Fin n) F)) := fK.comp (C g * X)
    syl fbar (derivative fbar) k (k - 1) =
      Matrix.diagonal (fun i : Fin (k + (k - 1)) => (g ^ ((i : ℕ) + 1))⁻¹) *
        syl fK (derivative fK) k (k - 1) *
        Matrix.diagonal (fun j : Fin (k + (k - 1)) =>
          if (j : ℕ) < k - 1 then g ^ (k + 1 + (j : ℕ)) else g ^ (k + 1 + ((j : ℕ) - (k - 1)))) := by sorry

end SparseLowFactors.BoundedDeg
