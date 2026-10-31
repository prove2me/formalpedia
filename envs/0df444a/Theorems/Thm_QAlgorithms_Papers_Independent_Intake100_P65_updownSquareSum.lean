-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_updownSquareSum
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.updownSquareSum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:22:51.764983+00:00
-- url     : https://prove2.me/theorems/cd745992-d2b3-462c-b64b-997b1534cd70
-- title:
--   Sum of squared updown-tableau counts
-- statement:
--   Let $n,r\ge1$. For each $0\le m\le\lfloor n/2\rfloor$ and each $r$-multipartition $\lambda$ of $n-2m$, let $f^{(n,\lambda)}=|T_n^{\mathrm{ud}}(\lambda)|$. Then
--
--   $$\sum_{m=0}^{\lfloor n/2\rfloor}\ \sum_{\lambda\vdash n-2m}\bigl(f^{(n,\lambda)}\bigr)^2=r^n(2n-1)!!.$$
--
--   The formal statement counts the finite disjoint union of pairs of paths with the same terminal shape, binding both $m$ and $\lambda$. This is exactly the displayed sum of squares.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 36, Corollary 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Corollary 5.2, PDF p.36: the sum of squared updown-path counts is the
cardinality of the indicated disjoint union, with no free shape or m. -/
theorem updownSquareSum (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    Finite (TerminalPathPairs r n) ∧
      Nat.card (TerminalPathPairs r n) = r^n * oddPairingCount n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
