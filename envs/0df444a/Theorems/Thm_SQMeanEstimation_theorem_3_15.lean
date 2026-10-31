-- Prove2me | Theorems.Thm_SQMeanEstimation_theorem_3_15
-- name    : SQMeanEstimation.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:49.834146+00:00
-- url     : https://prove2.me/theorems/8e030f43-74e2-42b5-ad3f-1e0bdd28319a
-- title:
--   Theorem 3.15 (corrected: d ≥ 2) — $\ell_q$ mean estimation, $q\in(1,2)$, with $2d\log d$ queries to $\mathrm{VSTAT}((16\log d/\varepsilon)^p)$
-- statement:
--   Let $q\in(1,2)$, let $p=q/(q-1)$ be its conjugate exponent, let $\varepsilon>0$ and $d\ge2$. Then there is a deterministic non-adaptive statistical query algorithm on $\mathbb R^d$ using at most
--   $$
--   m\le 2d\log_2 d
--   $$
--   queries such that, for every Borel probability distribution $\mu$ on $\mathbb R^d$ supported on the unit ball $B_q^d$ and every vector of answers that the oracle
--   $$
--   \mathrm{VSTAT}_\mu\Big(\Big(\frac{16\log_2 d}{\varepsilon}\Big)^{p}\Big)
--   $$
--   may return to its queries, the output $\tilde w$ satisfies $\|\mathbf E_{\mathbf w\sim\mu}[\mathbf w]-\tilde w\|_q\le\varepsilon$.
--
--   In words: the $\ell_q$ mean estimation problem with error $\varepsilon$ can be solved with $2d\log d$ queries to $\mathrm{VSTAT}((16\log(d)/\varepsilon)^p)$. This is the paper's nearly optimal estimation complexity for $q\in(1,2)$, matching its lower bounds up to the $\log d$ factor.
--
--   **Formalization Note** The algorithm is required to succeed against every behaviour of the oracle allowed by Definition 2.1, not only against the true means.
--
--   Differences from the source:
--   - correction: every d → d ≥ 2; reason: false at d = 1: 2·1·log 1 = 0 queries are allowed, so the output is a constant c, and for ε ∈ (0,1) it cannot satisfy both |c − 1| ≤ ε (μ = δ₁) and |c + 1| ≤ ε (μ = δ₋₁), both supported on B¹_q
--   - reading: log → Real.logb 2; reason: the ring thresholds of the proof are powers of 2, and its step 2^{1−⌊log(d)/q⌋} ≤ 4d^{−1/q} (p.18) holds only in base 2
--   - reading: using 2d log d queries → at most 2d·log₂ d queries (m ≤ 2d log₂ d); reason: 2d log₂ d need not be an integer, and unused queries can be padded
--   - encoding: VSTAT(n) with n an integer → real parameter (16·log₂ d/ε)^{q/(q−1)}; reason: the theorem's own parameter is not an integer
--   - generalization: an SQ algorithm (possibly adaptive or randomized) → a deterministic non-adaptive algorithm that succeeds against every valid answer vector; reason: such an algorithm is an SQ algorithm, and the paper's upper bounds are non-adaptive (Table 1, p.4), so the statement implies the source's claim
--   - encoding: distribution D supported on B_q^d; queries φ : B_q^d → [0,1] → Borel probability measure μ on Fin d → ℝ with lqNorm q w ≤ 1 μ-a.s.; measurable queries on all of ℝᵈ into [0,1]; reason: every query on the ball extends measurably to ℝᵈ, and values off the support do not affect the answers
--   - encoding: E_{w∼D}[w] → Bochner integral ∫ w, w ∂μ; reason: the identity is a.s. bounded, hence integrable
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Theorem 3.15, p.17

import Mathlib
import Definitions.Def_SQMeanEstimation_NonadaptiveSQ
import Definitions.Def_SQMeanEstimation_SolvesLqMeanEstimation

namespace SQMeanEstimation

/-- **Theorem 3.15 (corrected: d ≥ 2) — ℓq mean estimation for q ∈ (1, 2).**
Feldman, Guzmán, Vempala, *Statistical Query Algorithms for Mean Vector Estimation and Stochastic
Convex Optimization*, arXiv:1512.09170v2, Theorem 3.15, p.17: "For any q ∈ (1, 2) and ε > 0, the
ℓq mean estimation problem can be solved with error ε using 2d log d queries to
VSTAT((16 log(d)/ε)^p)." Here `p = q/(q−1)` is the conjugate exponent of `q` (§2, p.10).

For every `q ∈ (1, 2)`, `ε > 0` and `d ≥ 2` there are `m ≤ 2d·log₂ d` and a deterministic
non-adaptive SQ algorithm with `m` queries into `[0, 1]` such that, for every Borel probability
measure `μ` on ℝᵈ supported on the unit ℓq ball and every answer vector that
VSTAT_μ((16·log₂(d)/ε)^{q/(q−1)}) may return, the output is within ℓq distance `ε` of `E_μ[w]`.

**Formalization Note.** `d ≥ 2` corrects the statement: for `d = 1` it allows `2·1·log 1 = 0`
queries, and a constant output cannot be `ε`-close (`ε < 1`) to both `E_{δ₁}[w] = 1` and
`E_{δ₋₁}[w] = −1`. `log` is `Real.logb 2`. The VSTAT parameter is a real number. The algorithm is
non-adaptive and deterministic and must succeed against every valid oracle answer, as the paper's
upper bounds are (Table 1, p.4); this implies the paper's claim. -/
theorem theorem_3_15 (q ε : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hε : 0 < ε) (d : ℕ) (hd : 2 ≤ d) :
    ∃ m : ℕ, (m : ℝ) ≤ 2 * d * Real.logb 2 d ∧
      ∃ A : NonadaptiveSQ d m,
        SolvesLqMeanEstimation q ε ((16 * Real.logb 2 d / ε) ^ (q / (q - 1))) A := by sorry

end SQMeanEstimation
