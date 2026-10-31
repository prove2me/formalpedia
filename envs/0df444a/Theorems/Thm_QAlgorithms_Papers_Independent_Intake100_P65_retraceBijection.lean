-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_retraceBijection
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.retraceBijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:20:51.205218+00:00
-- url     : https://prove2.me/theorems/d53a52ff-7241-4e61-8d17-eb7c7095804b
-- title:
--   The retracing path class is the full add/remove boundary
-- statement:
--   Let $n,r\ge1$, $0\le m\le\lfloor n/2\rfloor$, and let $\lambda$ be an $r$-multipartition of $n-2m$. An updown $\lambda$-tableau is a path $t=(t_0,\ldots,t_n)$ starting at the empty multipartition and ending at $\lambda$, with one box added or removed at every step. For $1\le k<n$, suppose $t_{k-1}=t_{k+1}$. Then there is a bijection
--
--   $$\{\text{addable and removable nodes of }t_{k-1}\}\ \simeq\ \{s\in T_n^{\mathrm{ud}}(\lambda):s_j=t_j\text{ for }j\ne k\}.$$
--
--   Both additions and removals are included. This describes the local path choices in a retrace.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 18, Lemma 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Lemma 4.2, PDF p.18: the full add/remove boundary is in bijection with
the k-equivalence class of a retracing updown path. -/
theorem retraceBijection (r n m : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hm : m ≤ n/2) (lambda : MultipartitionShape r) (hsize : lambda.val.card = n-2*m)
    (t : Updown r n lambda) (k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (hreturn : pathAt t (k-1) = pathAt t (k+1)) :
    Nonempty (BoundaryNodes (pathAt t (k-1)) ≃
      {s : Updown r n lambda // KEquivalent k s t}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
