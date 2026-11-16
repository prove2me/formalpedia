-- Prove2me | Theorems.Thm_ParallelHAC_Supplement_theorem_8_ward_cc_hard
-- name    : ParallelHAC.Supplement.theorem_8_ward_cc_hard
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:35:29.144838+00:00
-- url     : https://prove2.me/theorems/50d0fb98-3f79-4031-b287-537584b59f7e
-- title:
--   Theorem 8 — $(1+\gamma/n)$-approximate promise merge Ward's HAC is CC-hard in $\mathbb R^{O(\log n)}$
-- statement:
--   There is a universal constant $\gamma>0$ such that $(1+\gamma/n)$-approximate promise merge HAC with $d_{\mathrm{Ward}}$, for $n$ points, is CC-hard in $\mathbb R^{O(\log n)}$, even on instances with constant aspect ratio. That is, there are constants $\gamma>0$, $c_D$ and $A$ such that every language in CC reduces, by a deterministic logspace many-one reduction, to the promise problem whose instances are $n\ge2$ distinct rational points in $\mathbb R^k$ with $k\le c_D\log_2 n$, Ward's aspect ratio at most $A$, and two designated points $a,b$, under the promise that the cluster $\{a,b\}$ appears in every $(1+\gamma/n)$-approximate HAC with $d_{\mathrm{Ward}}$ or in none, and whose answer is YES when it appears in every such HAC.
--
--   Since Ward's linkage is well-behaved (Theorem 2), the result shows that low dimension is necessary for the efficient parallel algorithms of the paper, unless CC-hard problems have NC algorithms.
--
--   **Formalization Note** The promise problem is `wardPromiseMerge γ cD A` and CC-hardness is `CCHard` (Definition 7, with CC the logspace closure of Comparator Circuit Value).
--
--   Differences from the source:
--   - encoding: an instance (P ⊆ ℝ^k, d, a, b) of promise merge HAC → a bit string encoding k, n, n distinct points with rational coordinates (sign, numerator, positive denominator in self-delimiting binary) and the positions of a, b; d fixed to d_Ward; reason: a logspace reduction outputs strings; rational coordinates are what the reduction of §6 outputs (p.50); hardness on this smaller domain implies hardness on any larger one
--   - encoding: in ℝ^{O(log n)}, even on instances with constant aspect ratio → ∃ cD A: the domain requires k ≤ cD · log₂ n and Ward's aspect ratio ≤ A (positive linkages between distinct points, any two within factor A); reason: pins O(·) and 'constant' by constants chosen before the input, together with γ
--   - reading: the class CC (not defined in the paper; [CFL14]) → languages deterministic-logspace many-one reducible to Comparator Circuit Value; reason: [CFL14] closes CCV under AC⁰ reductions; CC-hardness is the same for both closures, since an AC⁰ reduction is logspace and logspace reductions compose
--   - encoding: logspace-reducible (Definition 7) → ArrighiStarFree.HalfLevel.Reduces LogspaceComputable: a deterministic logspace transducer f with f x in the promise and the right answer for every string x; reason: the standard notion of reduction to a promise problem, from the published logspace layer
--   - encoding: the cluster {a, b} appears in a HAC → ∃ i ∈ [1, n − 1], R.A i ∪ R.B i = {a, b}; reason: a cluster of the dendrogram other than a leaf is the union of a merged pair
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.5, Theorem 8, p.13 (PDF p.16); restated p.43 (PDF p.46) and p.49 (PDF p.52), proof §6, pp.42–50 (PDF pp.45–53)

import Mathlib
import Definitions.Def_ParallelHAC_Supplement_CCHard
import Definitions.Def_ParallelHAC_Supplement_wardPromiseMerge

namespace ParallelHAC.Supplement

/-- **Theorem 8** (p.13): there is a universal constant `γ > 0` such that, for `n` points,
`(1 + γ/n)`-approximate promise merge HAC with `d_Ward` is CC-hard in `ℝ^{O(log n)}`, even on
instances with constant aspect ratio.

Formally: there are `γ > 0`, a dimension constant `cD` and an aspect-ratio constant `A` such that
the promise problem `wardPromiseMerge γ cD A` (instances with `n ≥ 2` distinct rational points
in `ℝ^k`, `k ≤ cD log₂ n`, Ward's aspect ratio at most `A`, under the promise that `{a, b}` appears
in every `(1 + γ/n)`-approximate HAC run or in none; answer YES if in every run) is CC-hard under
deterministic logspace many-one reductions (Definition 7).
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.5, Theorem 8, printed p.13 (PDF p.16); restated
p.43 (PDF p.46) and p.49 (PDF p.52), proof §6, pp.42–50.

**Formalization Note.** Instances are bit strings with rational coordinates in binary, the form
the reduction of §6 outputs (p.50). CC is the logspace closure of Comparator Circuit Value
(`InCC`); see `CCHard`. -/
theorem theorem_8_ward_cc_hard :
    ∃ γ : ℝ, 0 < γ ∧ ∃ cD A : ℝ, CCHard (wardPromiseMerge γ cD A) := by sorry

end ParallelHAC.Supplement
