-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_ma_not_subset_npbpp
-- name    : WatsonPseudodeterminism.MASeparation.ma_not_subset_npbpp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:43.601695+00:00
-- url     : https://prove2.me/theorems/b9166250-e960-4e52-8160-4fcf11c2f722
-- title:
--   Theorem 2 — MA is not contained in NP^BPP
-- statement:
--   There exists an infinite family $F$ of two-party partial Boolean functions on inputs of lengths $N_t\to\infty$ for which MA communication has polylogarithmic cost while N·BPP communication does not:
--
--   $$\exists F:\quad F\in\mathrm{MA}\ \land\ F\notin\mathrm{N\cdot BPP}.$$
--
--   In each class a single constant bounds the costs for the whole family by $C(\lfloor\log_2N_t\rfloor+1)^C$. The protocol models have at most $2^d$ witnesses, depth at most $d$, completeness $2/3$ and soundness $1/3$. N·BPP additionally imposes its acceptance gap for every witness on valid inputs only. The source identifies this class with $\mathrm{NP}^{\mathrm{BPP}}$. The theorem is proved in the source; this item requests its formal proof.
--
--   Differences from the source:
--   - reading: NP^BPP → N·BPP; reason: the paper explicitly identifies these classes on p. 2 and proves nonmembership in N·BPP in §4
--   - encoding: a set of at most 2^d distributions over depth-d protocols → an indexed family of k PMFs with k ≤ 2^d and support depth at most d; reason: duplicate indices do not change the represented set; every source distribution is represented and zero-mass trees do not affect the law
--   - encoding: infinite families with polylog N complexity → families with lengths tending to infinity and one natural C bounding costs by C(log₂ N + 1)^C; reason: this fixes the usual uniform polylogarithmic bound; finite exceptions can be absorbed in C without changing either class
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), Theorem 2, §1, p. 2; §1.1, pp. 3–4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Families

namespace WatsonPseudodeterminism.MASeparation

/-- Theorem 2, p. 2: MA is not contained in NP^BPP, identified there with N·BPP. -/
theorem ma_not_subset_npbpp :
    ∃ F : Family, InMA F ∧ ¬ InNBPP F := by sorry

end WatsonPseudodeterminism.MASeparation
