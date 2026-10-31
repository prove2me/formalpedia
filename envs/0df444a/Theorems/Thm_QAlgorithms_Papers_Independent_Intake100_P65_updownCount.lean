-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_updownCount
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.updownCount
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:21:50.711353+00:00
-- url     : https://prove2.me/theorems/78154c44-0b07-4dac-b49c-4984388c2f96
-- title:
--   Counting updown tableaux of a fixed terminal shape
-- statement:
--   Let $n,r\ge1$, $0\le m\le\lfloor n/2\rfloor$, and $\lambda$ an $r$-multipartition of $n-2m$. Let $f^{(n,\lambda)}=|T_n^{\mathrm{ud}}(\lambda)|$, and let $T^{\mathrm{std}}(\lambda)=T_{n-2m}^{\mathrm{ud}}(\lambda)$. These sets are finite and
--
--   $$f^{(n,\lambda)}=r^m\binom{n}{2m}(2m-1)!!\,|T^{\mathrm{std}}(\lambda)|.$$
--
--   The convention is $(-1)!!=1$. This is the multipartition extension of the updown-path count.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 35, Lemma 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 5.1, PDF p.35. The empty pairing product is one when m=0.
Finiteness is included explicitly before using natural cardinalities. -/
theorem updownCount (r n m : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hm : m ≤ n/2)
    (lambda : MultipartitionShape r) (hsize : lambda.val.card = n-2*m) :
    Finite (Updown r n lambda) ∧ Finite (Updown r (n-2*m) lambda) ∧
    Nat.card (Updown r n lambda) =
      r^m * n.choose (2*m) * oddPairingCount m * Nat.card (Updown r (n-2*m) lambda) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
