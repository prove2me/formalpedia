-- Prove2me | Theorems.Thm_SQMeanEstimation_ring_decomposition
-- name    : SQMeanEstimation.ring_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:58.405988+00:00
-- url     : https://prove2.me/theorems/fc9b5fc5-4a3b-42d4-b224-766261e17819
-- title:
--   Proof of Theorem 3.15 — ring decomposition $w=\sum_{j=0}^k[R_j(w^+)-R_j(w^-)]+[R_\infty(w^+)-R_\infty(w^-)]$ and $2^j(R_j(w^+))_i\in[0,1]$
-- statement:
--   1. For every integer $k$ and every $w\in\mathbb R^d$ with $|w_i|\le1$ for all $i$ (in particular every $w$ in the unit ball $B_q^d$),
--   $$
--   w=\sum_{j=0}^{k}\big[R_j(w^+)-R_j(w^-)\big]+\big[R_\infty(w^+)-R_\infty(w^-)\big],
--   $$
--   where $R_\infty$ uses the threshold $2^{-k-1}$ and the sum is empty when $k<0$.
--   2. For every $w\in\mathbb R^d$, every $j\in\mathbb N$ and every coordinate $i$,
--   $$
--   0\le 2^j\cdot(R_j(w^+))_i\le1 .
--   $$
--
--   Part 1 splits a point of the ball into pieces of dynamic range $2$; part 2 says that $\phi_i(w)=2^j(R_j(w^+))_i$ is a legitimate VSTAT query with values in $[0,1]$.
--
--   Differences from the source:
--   - generalization: w ∈ B_q^d and k = ⌊log(d)/q⌋ − 2 → every w with |wᵢ| ≤ 1 for all i and every integer k; reason: ‖w‖_q ≤ 1 implies |wᵢ| ≤ 1, so the statement specializes to the paper's w and k
--   - encoding: Σ_{j=0}^k with k possibly negative → ∑ over Finset.range (k + 1).toNat, empty for k < 0; reason: the paper's k is negative for small d, where the sum has no terms
--   - encoding: x ∈ ℝᵈ, ‖x‖ₚ = (Σ|xᵢ|ᵖ)^{1/p} → x : Fin d → ℝ, lqNorm p x = (∑ i, |x i| ^ p) ^ (1/p) with Real.rpow; reason: Lean convention; same values (paper coordinate i is index i − 1)
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17

import Mathlib
import Definitions.Def_SQMeanEstimation_posPart
import Definitions.Def_SQMeanEstimation_negPart
import Definitions.Def_SQMeanEstimation_ringPart
import Definitions.Def_SQMeanEstimation_ringInf

namespace SQMeanEstimation

/-- **Ring decomposition of the positive and negative parts.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17: "Namely,
w = Σ_{j=0}^k [Rⱼ(w⁺) − Rⱼ(w⁻)] + [R_∞(w⁺) − R_∞(w⁻)], where k ≐ ⌊log(d)/q⌋−2" and "Note that
2ʲ·(Rⱼ(w⁺))ᵢ ∈ [0, 1] for all w and j."

1. For every integer `k` and every `w` with `|wᵢ| ≤ 1` for all `i` (in particular every `w` in
   the unit ℓq ball), `w = Σ_{j=0}^k [Rⱼ(w⁺) − Rⱼ(w⁻)] + [R_∞(w⁺) − R_∞(w⁻)]`, the sum being
   empty when `k < 0`.
2. For every `w`, every `j` and every `i`, `0 ≤ 2ʲ·(Rⱼ(w⁺))ᵢ ≤ 1`.

**Formalization Note.** The sum `Σ_{j=0}^k` is over `Finset.range (k + 1).toNat`. The statement
holds for every `k : ℤ`, in particular for the paper's `k = ⌊log₂(d)/q⌋ − 2` (`ringDepth d q`). -/
theorem ring_decomposition {d : ℕ} :
    (∀ (k : ℤ) (w : Fin d → ℝ), (∀ i, |w i| ≤ 1) →
      w = (∑ j ∈ Finset.range (k + 1).toNat, (ringPart j (posPart w) - ringPart j (negPart w)))
        + (ringInf k (posPart w) - ringInf k (negPart w))) ∧
    (∀ (w : Fin d → ℝ) (j : ℕ) (i : Fin d),
      0 ≤ (2 : ℝ) ^ j * ringPart j (posPart w) i ∧ (2 : ℝ) ^ j * ringPart j (posPart w) i ≤ 1)
    := by sorry

end SQMeanEstimation
