-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_multipartition_partition_bijection
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.multipartition_partition_bijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:19:59.350036+00:00
-- url     : https://prove2.me/theorems/2958b570-848b-48bb-9701-31e25c899f1c
-- title:
--   The explicit multipartition–partition bijection
-- statement:
--   Let $l\ge1$ and $d\ge0$. Let $M_d(l)$ be the set of $l$-tuples of partitions of total size $d$ and let
--
--   $$P_d(l)=\left\{\mu:\ell(\mu)+\sum_j\lfloor\mu_j/l\rfloor\le d\right\}.$$
--
--   For $\lambda\in M_d(l)$, replace each part $a$ of color $r\in\{0,\ldots,l-1\}$ by $(a-1)l+r$ and omit any zero outputs. The resulting ordinary partition defines a bijection
--
--   $$\phi:M_d(l)\longrightarrow P_d(l).$$
--
--   In particular $|M_d(l)|=|P_d(l)|$. The inverse restores the missing zero parts using the total size $d$; color-zero singleton parts are not permanently discarded.
--
--   This identifies the two concrete indexing sets for the central bases.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 9, §2, unnumbered: multipartition–partition bijection

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- The explicit multipartition--partition bijection phi, PDF p.9.
The membership, injectivity, and full surjectivity clauses express a bijection
without making its range or either inverse identity a hypothesis. -/
theorem multipartition_partition_bijection (l d : ℕ) (hl : 0 < l) :
    (∀ lam : Multipartition l d,
      IsPartition (partitionPhi l lam.val) ∧
        (partitionPhi l lam.val).card + quotientSize l (partitionPhi l lam.val) ≤ d) ∧
    Function.Injective (fun lam : Multipartition l d => partitionPhi l lam.val) ∧
    (∀ mu : PartitionIndex l d, ∃ lam : Multipartition l d,
      partitionPhi l lam.val = mu.val) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
