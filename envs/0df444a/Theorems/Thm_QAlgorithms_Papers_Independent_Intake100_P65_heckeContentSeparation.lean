-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_heckeContentSeparation
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.heckeContentSeparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:23:17.155469+00:00
-- url     : https://prove2.me/theorems/38281d49-4d95-49ff-9655-d857a2ea7e78
-- title:
--   Standard tableaux across all shapes are separated by contents
-- statement:
--   Let $R$ be a field with $2$ invertible and characteristic zero or greater than $n$, where $n,r\ge1$. Let $u\in R^r$ be Hecke-generic: for distinct $i,j$, an integer collision $u_i-u_j=d$ implies $|d|\ge n$. Let $s$ and $t$ be standard tableaux of arbitrary $r$-multipartition shapes $\lambda,\mu\vdash n$, with contents $c_s(k),c_t(k)$ as above. Then
--
--   $$s=t\quad\Longleftrightarrow\quad c_s(k)=c_t(k)\quad(1\le k\le n).$$
--
--   Equality on the left includes equality of terminal shapes. This supplies separation in the disjoint union of all standard tableaux.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 42, Lemma 6.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 6.5, PDF p.42. Equality is compared in the disjoint union of
standard tableaux of all shapes, via the full shape sequence; this includes
lambda=mu in the conclusion rather than assuming it. Printed char R>n
includes characteristic zero, as required by the real specialization on p.41;
HeckeGeneric uses the distinct-index correction specified in its definition. -/
theorem heckeContentSeparation (R : Type u) [Field R] [Invertible (2 : R)]
    (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (roots : Fin r → R)
    (hg : HeckeGeneric n roots) (hchar : ringChar R = 0 ∨ n < ringChar R)
    (lambda mu : MultipartitionShape r) (hlambda : lambda.val.card = n) (hmu : mu.val.card = n)
    (s : Updown r n lambda) (t : Updown r n mu) :
    s.val = t.val ↔ ∀ k : Fin n, content roots s (k.val+1) = content roots t (k.val+1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
