-- Prove2me | Theorems.Thm_RSBDDHard_identity_3
-- name    : RSBDDHard.identity_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:42.92078+00:00
-- url     : https://prove2.me/theorems/e7ffccf8-66b4-4973-af34-48b619c1341d
-- title:
--   Identity (3) — the first two power sums from the first two coefficients of $P_S$
-- statement:
--   Let $S$ be a finite set and write
--   $$P_S(Z)=\prod_{a\in S}(1-aZ)=1+c_1Z+c_2Z^2+\cdots.$$
--   Then
--   $$M_1(S)=-c_1,\qquad M_2(S)=c_1^2-2c_2.\tag{3}$$
--
--   Unlike Newton's identities in general, this needs no division, so it holds in characteristic $p$. It converts the prescribed coefficients of $P_S$ into the first two power sums in the soundness proof of Theorem 1.6.
--
--   Differences from the source:
--   - generalization: S a finite subset of the field F → S a finite subset of any commutative ring; reason: the identity uses no division; fields are instances
-- source:
--   Gandikota, Grigorescu, Venkitesh, NP-Hardness of Bounded Distance Decoding for Reed-Solomon Codes and Variants, via Non-Archimedean Rings, STOC 2027 submission (sha256 0372e933…), Identity (3), p.12

import Mathlib
import Definitions.Def_RSBDDHard_recipProd

set_option autoImplicit false

namespace RSBDDHard

/-- **Identity (3).** Gandikota, Grigorescu, Venkitesh, *NP-Hardness of Bounded Distance
Decoding for Reed-Solomon Codes and Variants, via Non-Archimedean Rings*, STOC 2027 submission
(sha256 0372e933…), p.12. Write `P_S(Z) = Π_{a ∈ S}(1 − aZ) = 1 + c_1 Z + c_2 Z² + ⋯`. Then
`M_1(S) = −c_1` and `M_2(S) = c_1² − 2c_2`.

**Formalization Note.** Stated for every finite set `S` in every commutative ring (the paper uses
it over the field `F`). -/
theorem identity_3 {R : Type*} [CommRing R] (S : Finset R) :
    powerSum S 1 = -(recipProd S).coeff 1 ∧
    powerSum S 2 = (recipProd S).coeff 1 ^ 2 - 2 * (recipProd S).coeff 2 := by sorry

end RSBDDHard
