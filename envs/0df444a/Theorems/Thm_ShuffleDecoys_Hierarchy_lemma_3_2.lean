-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_lemma_3_2
-- name    : ShuffleDecoys.Hierarchy.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:31.155562+00:00
-- url     : https://prove2.me/theorems/b121df83-12e9-4d9b-8958-541b22259001
-- title:
--   Lemma 3.2 — pairwise square-root distance bound: I(M; T) ≤ 2 Σ_{i<j} max{p_i, p_j} ‖√W_i − √W_j‖²₂
-- statement:
--   Let $M$ take values in $[d]$ with prior probabilities $p_1,\dots,p_d>0$, and let $W_i=\mathrm{Law}(T\mid M=i)$ be probability mass functions on a common discrete output space. Then
--   $$I(M;T)\ \le\ 2\sum_{1\le i<j\le d}\max\{p_i,p_j\}\,\big\|\sqrt{W_i}-\sqrt{W_j}\big\|_2^2,\qquad \big\|\sqrt A-\sqrt B\big\|_2^2:=\sum_t\big(\sqrt{A(t)}-\sqrt{B(t)}\big)^2.$$
--   The bound holds even when the conditional laws have different supports; it converts pairwise shift estimates into an upper bound on leakage.
--
--   Differences from the source:
--   - encoding: "a common discrete output space" → an arbitrary type $\beta$ with laws `PMF β` (countable supports); joint law `channelJoint p W`; reason: a PMF is exactly a discrete law, on any type.
--   - encoding: $\sum_{1\le i<j\le d}$ → $\sum_{i,j\in\texttt{Fin }d}$ restricted to $i<j$; reason: same index set, 0-based.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 17, Lemma 3.2, Eq. (7)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Lemma 3.2: for `M` on `[d]` with every `pᵢ > 0` and conditional laws `Wᵢ = Law(T | M = i)`
on a common discrete output space,
`I(M; T) ≤ 2 Σ_{i<j} max{pᵢ, pⱼ} ‖√Wᵢ − √Wⱼ‖₂²` (nats). -/
theorem lemma_3_2 {β : Type*} (d : ℕ) (p : PMF (Fin d)) (hp : ∀ i, 0 < p i)
    (W : Fin d → PMF β) :
    mutualInfo (channelJoint p W) ≤
      ENNReal.ofReal (2 * ∑ i : Fin d, ∑ j : Fin d,
        if i < j then max (p i).toReal (p j).toReal * sqrtDistSq (W i) (W j) else 0) := by sorry

end ShuffleDecoys.Hierarchy
