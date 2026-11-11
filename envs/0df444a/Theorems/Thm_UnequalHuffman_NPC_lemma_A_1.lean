-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_A_1
-- name    : UnequalHuffman.NPC.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:21.986851+00:00
-- url     : https://prove2.me/theorems/7b646fdd-d8ea-49a5-9023-981d9afb341f
-- title:
--   Lemma A.1 — the interval identity: a linear score equals the weighted quadratic interval penalty plus a constant
-- statement:
--   Let interval data $[\ell_{t,k}, r_{t,k}]$ be given for the sorted leaf positions of a leaf profile $(n_1,\dots,n_H)$: integer endpoints, width at most one, both endpoint lists nondecreasing at each depth. Suppose some full ordered tree with this profile satisfies all intervals. Let $g_{t,k} = -2^{H-t}(\ell_{t,k} + r_{t,k} + H - t)$ and $Q_0 = -S^* - \sum_{t,k} 2^{H-t}\ell_{t,k}r_{t,k}$ with $S^* = \sum_{t=0}^{H-1} I_t 2^{H-t-1}(H-t)$. Then every row $(g_{t,k})_k$ is nonincreasing, and every full ordered tree $T$ with this leaf profile satisfies
--   $$Q(T) - Q_0 = \sum_{t,k} 2^{H-t}(z_{t,k} - \ell_{t,k})(z_{t,k} - r_{t,k}),\qquad Q(T) = \sum_{t,k} g_{t,k} z_{t,k}; \tag{19}$$
--   consequently $Q(T) \ge Q_0$, $Q(T) = Q_0$ exactly when $T$ respects all intervals, and $Q(T) \ne Q_0$ implies $Q(T) \ge Q_0 + 1$.
--
--   Source (p. 39): "Lemma A.1. Fix a realizable sequence $I_0,\dots,I_H$ and intervals as above, and suppose that some coordinate profile satisfies all intervals. There are explicit integers $g_{t,k}$ and $Q_0$ such that the lists $(g_{t,k})_k$ are nonincreasing and, for every tree with these internal-vertex counts, (19). Consequently, $Q(T) \ge Q_0$, with equality exactly on the interval-respecting trees, and every positive difference is at least one."
--
--   Differences from the source:
--   - generalization: there are explicit integers g_{t,k} and Q0 → the specific integers of the proof (p. 39): g_{t,k} = −2^{H−t}(ℓ + r + H − t), Q0 = −S* − Σ 2^{H−t} ℓ r; reason: stating the proof's explicit values implies the existential
--   - generalization: H the height of the realizable sequence (n_H > 0) → H = number of interval rows; trailing depths without leaves allowed; reason: the identity holds for every such H; it specializes to the height
--   - reading: every tree with these internal-vertex counts → every full ordered tree with the leaf profile n_t = |row t| (equivalently internal counts I_t, n_t = 2I_{t−1} − I_t); reason: the trees of Appendix A are the full trees of the leaf-profile problem; internal and leaf counts determine each other
--   - encoding: a realizable I_0, …, I_H; some coordinate profile satisfies all intervals → hypothesis: some full tree with the profile respects the intervals (realizability follows); reason: §2.1 (p. 8): coordinate profiles are exactly those realized by full trees
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 39, Lemma A.1 (coefficients from its proof)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_IntervalPenalty

namespace UnequalHuffman.NPC

open IntervalData

/-- Lemma A.1 (p. 39), with the explicit integers of its proof,
`g_{t,k} = -2^{H-t}(ℓ_{t,k} + r_{t,k} + H - t)` and `Q₀ = -S* - ∑_{t,k} 2^{H-t} ℓ_{t,k} r_{t,k}`:
if some full tree with the leaf profile satisfies all intervals, then the rows `(g_{t,k})_k` are
nonincreasing and every full tree `T` with this profile satisfies
`Q(T) - Q₀ = ∑_{t,k} 2^{H-t}(z_{t,k} - ℓ_{t,k})(z_{t,k} - r_{t,k})`; consequently `Q(T) ≥ Q₀`,
with equality exactly on the interval-respecting trees, and every positive difference is at
least one. -/
theorem lemma_A_1 (J : IntervalData) (hJ : J.IsIntervalSystem)
    (hsat : ∃ T : OTree, IsProfileTree J.counts T ∧ J.Respects T) :
    (∀ t, (J.gRow t).Pairwise (· ≥ ·)) ∧
    ∀ T : OTree, IsProfileTree J.counts T →
      J.Q T - J.Q0 = J.penalty T ∧
      J.Q0 ≤ J.Q T ∧
      (J.Q T = J.Q0 ↔ J.Respects T) ∧
      (J.Q T ≠ J.Q0 → J.Q0 + 1 ≤ J.Q T) := by sorry

end UnequalHuffman.NPC
