-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_labelledBrauer_card
-- name    : QAlgorithms.Papers.Independent.Support21.P14.labelledBrauer_card
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:32:58.019417+00:00
-- url     : https://prove2.me/theorems/75f61505-a4e3-450e-aec1-1950671d8683
-- title:
--   Number of cyclically labelled Brauer diagrams
-- statement:
--   Let $n\ge0$ and $r\ge1$. A $\mathbb Z_r$-Brauer diagram is a pairing of the $2n$ distinguished upper and lower boundary endpoints, with one cyclic-group label on each oriented strand; reversing an orientation negates its label. Crossings and planar drawings are not part of the pairing data. With the empty-product convention $(-1)!!=1$,
--   $$\#\{\mathbb Z_r\text{-Brauer diagrams on }n\text{ strands}\}=r^n(2n-1)!!=r^n\prod_{k=0}^{n-1}(2k+1).$$
--   In particular, there is exactly one empty diagram. This gives the combinatorial dimension used for the labelled Brauer algebra.
--
--   **Formalization Note** Each strand is canonically oriented from its smaller endpoint to its larger endpoint; its cyclic label is stored by its representative in $\{0,\ldots,r-1\}$.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 43, Section 5 unnumbered: number of Z_r-labelled Brauer diagrams

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Unnumbered labelled Brauer-diagram count, §5, PDF p.43.
Includes n=0, where both the empty pairing and its empty labelling are unique. -/
theorem labelledBrauer_card (n r : ℕ) (hr : 0 < r) :
    Nat.card (LabelledBrauerDiagram n r) = r^n * oddPairingCount n := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
