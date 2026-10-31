-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_contentSeparation
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.contentSeparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:21:27.643725+00:00
-- url     : https://prove2.me/theorems/2590d193-d488-4c39-bd70-3f71b9e99672
-- title:
--   All four generic-content separation properties
-- statement:
--   Let $R$ be a commutative unital ring with $2$ invertible, $n,r\ge1$, and characteristic zero or characteristic greater than $2n$. Let $u\in R^r$ be $W$-generic: each integer collision $u_i\pm u_j=d$ for $i\ne j$, or $2u_i=d$, has $|d|\ge2n$. Let $\lambda\vdash n-2m$ with $0\le m\le\lfloor n/2\rfloor$, and $t,s\in T_n^{\mathrm{ud}}(\lambda)$. The signed content at time $k$ is $c_t(k)=u_h+j-i$ for adding node $(i,j,h)$ and its negative for removal. Then
--
--   $$t=s\iff c_t(k)=c_s(k)\ (1\le k\le n),\qquad c_t(k)-c_t(k+1)\ne0\ (1\le k<n).$$
--
--   If $t_{k-1}=t_{k+1}$, $s$ differs from $t$ only at time $k$, and $s\ne t$, then both $c_t(k)+c_s(k)$ and $c_t(k)-c_s(k)$ are nonzero. Finally $2c_t(k)+1\ne0$ and $2c_t(k)-1\ne0$ for every $1\le k\le n$. These are conclusions of genericity, used to justify the later denominators.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 18, Lemma 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 4.4, PDF p.18, all four clauses. Characteristic zero is included;
the statement is over rings as printed, not restricted to fields. All
nonvanishing conditions are conclusions of genericity. Printed char R>2n
is read as char zero or char R>2n: the paper applies these results over the
real numbers in section 5. -/
theorem contentSeparation (R : Type u) [CommRing R] [Invertible (2 : R)]
    (r n m : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hm : m ≤ n/2)
    (lambda : MultipartitionShape r) (hsize : lambda.val.card = n-2*m)
    (roots : Fin r → R) (hg : WGeneric n roots)
    (hchar : ringChar R = 0 ∨ 2*n < ringChar R)
    (t s : Updown r n lambda) :
    (t = s ↔ ∀ k : Fin n, content roots t (k.val+1) = content roots s (k.val+1)) ∧
    (∀ k : ℕ, 1 ≤ k → k < n → content roots t k - content roots t (k+1) ≠ 0) ∧
    (∀ k : ℕ, 1 ≤ k → k < n → pathAt t (k-1) = pathAt t (k+1) →
      KEquivalent k s t → s ≠ t →
        content roots t k + content roots s k ≠ 0 ∧ content roots t k - content roots s k ≠ 0) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n →
      2 * content roots t k + 1 ≠ 0 ∧ 2 * content roots t k - 1 ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
