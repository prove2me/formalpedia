-- Prove2me | Theorems.Thm_RSSubspaceDesign_theorem_2_14
-- name    : RSSubspaceDesign.theorem_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:23:31.269443+00:00
-- url     : https://prove2.me/theorems/04873657-90ac-4bb3-a5e5-c07b8a1dbdb5
-- title:
--   Theorem 2.14 (Cauchy–Binet)
-- statement:
--   Let $E$ be a field and $1\le t\le e$. For $B\in E^{t\times e}$ and $D\in E^{e\times t}$,
--   $$\det(BD)=\sum_{\substack{S\subseteq[e]\\|S|=t}}\det B_{[t],S}\,\det D_{S,[t]},$$
--   where the submatrices use the indicated rows and columns in increasing order.
--
--   In the proof of Proposition 4.3 this expresses the determinant of a change of basis as a $K$-combination of the maximal minors of a fixed polynomial matrix.
--
--   Differences from the source:
--   - encoding: index sets [e], [t] and the sum over S ⊆ [e] with |S| = t, rows and columns in increasing order → Fin e, Fin t; the sum over the subtype {S // S.card = t}, S listed by its increasing enumeration orderEmbOfFin; reason: Lean convention; same matrices and index set
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 2.14, p.13 (PDF p.15)

import Mathlib

namespace RSSubspaceDesign

/-- **Theorem 2.14 (Cauchy–Binet).** Alrabiah–Goyal–Guruswami, *Explicit Reed-Solomon Subspace
Designs: Optimal List and Line Decoding*, arXiv:2610.36215 (held version, sha256
cf26424b…f36206), Theorem 2.14, p.13.

Let `E` be a field and `1 ≤ t ≤ e`. For `B ∈ E^{t×e}` and `D ∈ E^{e×t}`,
`det(BD) = ∑_{S ⊆ [e], |S| = t} det B_{[t],S} · det D_{S,[t]}`, the submatrices using the indicated
rows and columns in increasing order.

**Formalization Note.** Indices are `Fin t`, `Fin e`. The sum runs over the subtype of `t`-element
subsets `S`, and `S.orderEmbOfFin` lists `S` in increasing order. -/
theorem theorem_2_14 {E : Type*} [Field E] {t e : ℕ} (ht : 1 ≤ t) (hte : t ≤ e)
    (B : Matrix (Fin t) (Fin e) E) (D : Matrix (Fin e) (Fin t) E) :
    (B * D).det = ∑ S : {S : Finset (Fin e) // S.card = t},
      (B.submatrix id (S.1.orderEmbOfFin S.2)).det * (D.submatrix (S.1.orderEmbOfFin S.2) id).det := by sorry

end RSSubspaceDesign
