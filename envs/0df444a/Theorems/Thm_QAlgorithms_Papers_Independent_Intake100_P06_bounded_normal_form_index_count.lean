-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_bounded_normal_form_index_count
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.bounded_normal_form_index_count
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:46:23.032533+00:00
-- url     : https://prove2.me/theorems/3e26ecef-1ab8-4907-9b38-273693518f05
-- title:
--   Count of bounded normal-form indices
-- statement:
--   Let $n\ge0$ and $r\ge1$ be integers. Pair the $2n$ boundary vertices in unordered pairs and assign to each pair one label in $\{0,\ldots,r-1\}$, using the orientation from its smaller numbered endpoint to its larger numbered endpoint. Let $I_{n,r}$ be this set of labelled pairings, which indexes the bounded normal-form words in Section 3.4. Then
--   $$|I_{n,r}|=r^n\prod_{k=0}^{n-1}(2k+1)=r^n(2n-1)!!.$$
--   The empty pairing has exactly one empty labelling, so the value at $n=0$ is $1$.
--
--   This counts the indexed words independently of their possibly coincident images in a specialized algebra; it makes no independence assertion before admissibility.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 30, Section 3.4: size of the bounded normal-form index family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Section 3.4, PDF p.30: bounded normal-form INDEX count, independently of
possibly coincident specialized images. Label each strand once; n=0 gives 1. -/
theorem bounded_normal_form_index_count (n r : ℕ) (hr : 0 < r) :
    Nat.card (LabelledBrauerDiagram n r) = r ^ n * oddPairingCount n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
