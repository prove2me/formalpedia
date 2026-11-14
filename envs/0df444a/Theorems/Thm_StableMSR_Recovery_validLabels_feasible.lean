-- Prove2me | Theorems.Thm_StableMSR_Recovery_validLabels_feasible
-- name    : StableMSR.Recovery.validLabels_feasible
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T14:31:12.239188+00:00
-- url     : https://prove2.me/theorems/ee6514fc-9b59-4fd9-9fca-ccc81a3e00ce
-- title:
--   Validated surjective output labels decode to an exact-k partition
-- statement:
--   Let $n,k\in\mathbb N$ and let $s$ be a machine state. Suppose the output label of every point is an integer in $\{0,\ldots,k-1\}$, and every one of these $k$ labels is used. Decode the labels into their unordered fibers. Then
--   $$\operatorname{outputPartition}(s)\text{ is a partition of all }n\text{ points into exactly }k\text{ nonempty blocks}.$$
--   No metric, stability, or positivity assumption on $n,k$ is needed. The statement includes $n=k=0$; if $k=0<n$, its hypotheses are impossible. This is the encoding lemma that derives the feasibility requirement in the recovery specification from the program's validated output labels.
--
--   **Formalization Note.** The labels, their validation, and their decoding are the existing canonical definitions in `StableMSR_Recovery_Execution`; this theorem adds no alternate output representation.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547v1, https://arxiv.org/html/2611.03547v1, Section 1 (exact-k partitions), Section 3 (computational model); elementary encoding consequence of the mission's canonical StableMSR_Recovery_Execution definitions ValidLabels and outputPartition.

import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem validLabels_feasible {n k : ℕ} (s : MinSumFPT.State)
    (h : ValidLabels n k s) : Feasible Finset.univ k (outputPartition n k s) := by sorry

end StableMSR.Recovery
