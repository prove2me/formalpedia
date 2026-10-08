-- Prove2me | Theorems.Thm_SchedComplexity_Partition_theorem_3_partition_reducible
-- name    : SchedComplexity.Partition.theorem_3_partition_reducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:40:14.172977+00:00
-- url     : https://prove2.me/theorems/e812bb2d-b18b-4b88-bfb5-639acc865cc8
-- title:
--   Theorem 3 — PARTITION $\propto n|2|I|C_{\max}$ and PARTITION $\propto n|2|I|\sum w_jC_j$
-- statement:
--   **Theorem 3** (Brucker, Lenstra & Rinnooy Kan). PARTITION is reducible to the following problems:
--
--   1. $n|2|I|C_{\max}$, minimizing the makespan on two identical machines;
--   2. $n|2|I|\sum w_jC_j$, minimizing the total weighted completion time on two identical machines.
--
--   "Reducible" ($P'\propto P$, Section 2) means polynomial-time many-one reducibility between the recognition languages: there is a function $f$, computable by a Turing machine in polynomial time, such that a word $x$ is the code of a yes-instance of PARTITION (positive integers) iff $f(x)$ is the code of an instance of the target problem together with a threshold $y$ for which some feasible schedule has value $\le y$:
--
--   $$L_{\mathrm{PARTITION}} \le_p L_{n|2|I|C_{\max}} \quad\text{and}\quad L_{\mathrm{PARTITION}} \le_p L_{n|2|I|\sum w_jC_j}.$$
--
--   Since PARTITION is NP-complete, both scheduling problems are NP-hard, already with two machines.
--
--   **Formalization Note** Reducibility is `CookPvsNP.PolyReducible` (one-tape Turing machines with an explicit polynomial time bound). All languages are over the four-letter alphabet `BSym` with binary number codes `encNats`. The target languages have natural-number thresholds; the paper's rational thresholds $\tfrac12A$ and $\sum_{j\le k}a_ja_k-\tfrac14A^2$ are replaced in the code by their floors, which give the same yes-instances because all schedule values are integers. The NP-membership statement of p. 8 is not part of this theorem.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 15, Theorem 3 (reducibility as defined on p. 4, Section 2)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_Partition_PartitionProblem
import Definitions.Def_SchedComplexity_Partition_Languages

namespace SchedComplexity.Partition

/-- Theorem 3 (Brucker, Lenstra & Rinnooy Kan 1975, p. 15): PARTITION is reducible (polynomial-time
many-one, `CookPvsNP.PolyReducible`) to (a) `n|2|I|C_max` and (b) `n|2|I|Σw_jC_j`. -/
theorem theorem_3_partition_reducible :
    CookPvsNP.PolyReducible partitionLang cmaxLang ∧
      CookPvsNP.PolyReducible partitionLang sumWCLang := by sorry

end SchedComplexity.Partition
