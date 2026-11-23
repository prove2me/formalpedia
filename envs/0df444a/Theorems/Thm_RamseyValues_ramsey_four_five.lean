-- Prove2me | Theorems.Thm_RamseyValues_ramsey_four_five
-- name    : RamseyValues.ramsey_four_five
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T00:03:37.464801+00:00
-- url     : https://prove2.me/theorems/f1465ccb-10ee-4bcb-b22a-e8f89cb32d1e
-- title:
--   $R(4,5)=25$
-- statement:
--   McKay and Radziszowski proved $R(4,5)=25$, the largest exact classical Ramsey value known: every simple graph on $25$ vertices contains a $4$-clique or a $5$-vertex independent set, and $24$ vertices do not suffice. Their proof combines high-level counting arguments with an exhaustive computer search. The value has since been given a machine-checked proof by Gauthier and Brown (ITP 2024).
--
--   **Formalization Note.** Stated as `Erdos77.asymmetricRamsey 4 5 = 25` over the platform Ramsey-number definition.
-- source:
--   B. D. McKay and S. P. Radziszowski, R(4,5)=25, J. Graph Theory 19 (1995) 309–322; see T. Gauthier and C. E. Brown, A Formal Proof of R(4,5)=25, ITP 2024, https://arxiv.org/abs/2404.01761 ; tabulated in Radziszowski, Small Ramsey Numbers, https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_four_five : Erdos77.asymmetricRamsey 4 5 = 25 := by sorry

end RamseyValues
