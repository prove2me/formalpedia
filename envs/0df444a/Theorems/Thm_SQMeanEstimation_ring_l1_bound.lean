-- Prove2me | Theorems.Thm_SQMeanEstimation_ring_l1_bound
-- name    : SQMeanEstimation.ring_l1_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:56.155981+00:00
-- url     : https://prove2.me/theorems/c734ccf1-cf34-439f-8a8f-93f52208f184
-- title:
--   Proof of Theorem 3.15 — $\|R_j(w^+)\|_1\le(2^{-j-1})^{1-q}\|R_j(w^+)\|_q^q\le(2^{-j-1})^{1-q}$ on $B_q^d$
-- statement:
--   Let $q\in(1,2)$, $j\in\mathbb N$ and $w\in\mathbb R^d$ with $\|w\|_q\le1$. Then
--   $$
--   \|R_j(w^+)\|_1\le(2^{-j-1})^{1-q}\,\|R_j(w^+)\|_q^q\le(2^{-j-1})^{1-q}.
--   $$
--
--   Since the nonzero coordinates of $R_j(w^+)$ exceed $2^{-j-1}$, its $\ell_1$ mass is controlled by its $\ell_q$ mass, which is at most that of $w$.
--
--   Differences from the source:
--   - encoding: ‖·‖₁ and ‖·‖_q^q → ∑ i, |x i| and ∑ i, |x i| ^ q; reason: the definitions of these quantities
--   - encoding: w ∈ B_q^d → lqNorm q w ≤ 1; reason: the unit ball of ‖·‖_q
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.18, display after "We next observe that by Lemma 3.12"

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_posPart
import Definitions.Def_SQMeanEstimation_ringPart

namespace SQMeanEstimation

/-- **ℓ₁ bound on a ring of the positive part.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, p.18: "We next observe that by Lemma 3.12, for every
w ∈ Bᵈ_q, ‖Rⱼ(w⁺)‖₁ ≤ (2^{−j−1})^{1−q}‖Rⱼ(w⁺)‖_q^q ≤ (2^{−j−1})^{1−q}."

For `q ∈ (1, 2)`, `j ∈ ℕ` and `w` with `‖w‖_q ≤ 1`, both inequalities of the chain hold.

**Formalization Note.** `‖·‖₁` is `Σ |·|` and `‖·‖_q^q` is `Σ |·|^q`. Powers are `Real.rpow`. -/
theorem ring_l1_bound {d : ℕ} (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (j : ℕ) (w : Fin d → ℝ)
    (hw : lqNorm q w ≤ 1) :
    ∑ i, |ringPart j (posPart w) i| ≤
        ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * ∑ i, |ringPart j (posPart w) i| ^ q ∧
      ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * ∑ i, |ringPart j (posPart w) i| ^ q ≤
        ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) := by sorry

end SQMeanEstimation
