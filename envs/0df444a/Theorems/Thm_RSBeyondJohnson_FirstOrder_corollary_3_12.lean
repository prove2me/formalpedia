-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_corollary_3_12
-- name    : RSBeyondJohnson.FirstOrder.corollary_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:06.799058+00:00
-- url     : https://prove2.me/theorems/94207b14-7c54-4ba1-b559-cc0b926b9ac1
-- title:
--   Corollary 3.12 — primitive polynomial kernel vector of degree at most ⌊Rb/(N_coef − R)⌋
-- statement:
--   Let $\mathbf A(Z)$ be a matrix over $F[Z]$ with finitely many rows and $N_{\mathrm{coef}}$ columns, of rank $R<N_{\mathrm{coef}}$ over the field of fractions $F(Z)$, whose entries have degree at most $b$. Then $\mathbf A(Z)v=0$ for some $v\in F[Z]^{N_{\mathrm{coef}}}$ whose entries have greatest common divisor one and degree at most
--   $$\Big\lfloor\frac{Rb}{N_{\mathrm{coef}}-R}\Big\rfloor;$$
--   in particular $v(z)\ne0$ for every $z$ in every extension field of $F$. It bounds the challenge degree of the symbolic explainer.
--
--   Differences from the source:
--   - encoding: rows of A(Z) → an arbitrary finite row type I (Lemma 3.11: finite sets I, J); reason: the corollary does not fix the number of rows
--   - encoding: rank R over F(Z) → Matrix.rank of A mapped into RatFunc F equals R; reason: RatFunc F is the fraction field F(Z)
--   - encoding: greatest common divisor one → every common divisor of the entries is a unit; reason: gcd in F[Z] up to units
--   - encoding: ⌊Rb/(N_coef − R)⌋ → R * b / (N − R) in ℕ; reason: natural division is the floor; N − R > 0
--   - encoding: every z in every extension of F → every field K : Type u with Algebra F K and z : K: the vector (aeval z (v j))_j is nonzero; reason: same universe as F; every extension's subfield F(z) has a copy there
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 20, Corollary 3.12

import Mathlib


open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Corollary 3.12 (Equal costs)**, p. 20. Let `A(Z)` be a polynomial matrix with `N_coef`
columns, rank `R < N_coef` over `F(Z)`, and entries of degree at most `b`. Then `A(Z) v = 0` for
some `v ∈ F[Z]^{N_coef}` whose entries have greatest common divisor one and degree at most
`⌊R b/(N_coef − R)⌋`; in particular `v(z) ≠ 0` for every `z` in every extension of `F`. -/
theorem corollary_3_12.{u, w} {F : Type u} [Field F] {I : Type w} [Fintype I] (N R b : ℕ)
    (A : Matrix I (Fin N) F[X])
    (hrank : (A.map (algebraMap F[X] (RatFunc F))).rank = R) (hRN : R < N)
    (hdeg : ∀ i j, (A i j).natDegree ≤ b) :
    ∃ v : Fin N → F[X], A.mulVec v = 0 ∧
      (∀ p : F[X], (∀ j, p ∣ v j) → IsUnit p) ∧
      (∀ j, (v j).natDegree ≤ R * b / (N - R)) ∧
      ∀ (K : Type u) [Field K] [Algebra F K] (z : K), (fun j => aeval z (v j)) ≠ 0 := by sorry

end RSBeyondJohnson.FirstOrder
