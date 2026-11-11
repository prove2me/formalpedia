-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_36
-- name    : WeakStrongMSR.lemma_3_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:31:55.560394+00:00
-- url     : https://prove2.me/theorems/252add04-970c-418e-b445-9cfe429ae21f
-- title:
--   Lemma 3.36 — whp the test at $\lambda_+$ passes and the test at $\lambda_-$ fails
-- statement:
--   Let $1\le k<n$, let $d$ be a metric with $\mathrm{aspect}(d)\le\Delta$, let $u,v$ be the points $0,1$, $d_0=d(u,v)$ and $C=3000$, and set
--   $$\lambda_-=\frac{d_0}{2Ck\Delta},\qquad\lambda_+=\frac{\Delta d_0}{k}.$$
--   A test passes if it does not abort and its total radius is at most $Ck\lambda$.
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there are $a>0$ and $n_0$ with the following property, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, adversary, LP routine selecting optimal solutions, $\varepsilon\in(0,1]$ and offline routine with guarantee $3+\varepsilon$. With probability at least $1-n^{-a}$ over the corruption set and the independent randomness of the two tests, the test at $\lambda_+$ passes and the test at $\lambda_-$ fails.
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - reading: "with high probability", "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ a > 0, ∃ n₀: probability ≥ 1 − n^{−a} for n ≥ n₀, with c₀, a, n₀ independent of δ; reason: §2.3: whp = 1 − n^{−Ω(1)}; App. A: every bound fails with probability n^{−Ω(c)} for an absolute c
--   - generalization: "solve (1)", "the (3+ϵ)-approximation of [BERW24]" → every LP routine selecting optimal solutions and every offline routine covering S with cost ≤ (3+ε)·opt_S; reason: the statement holds for every such routine, in particular for the paper's
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
--   - generalization: the known aspect-ratio bound Δ ≤ n^{O(1)} of §2.3 and Theorem 3.35 → any Δ ≥ aspect(d); no polynomial bound on Δ assumed; reason: the proof uses only d₀/Δ ≤ d_min and d_max ≤ Δd₀ (Eq. (17)) and Lemma 3.33 at two fixed guesses; the source case Δ ≤ n^{O(1)} is an instance
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.36, p.28 (PDF 29); Eqs. (17), (18), p.27 (PDF 28)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Sampling
import Definitions.Def_WeakStrongMSR_Rounding
import Definitions.Def_WeakStrongMSR_Repair
import Definitions.Def_WeakStrongMSR_Compress
import Definitions.Def_WeakStrongMSR_Test

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.36** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.28, PDF p.29; λ± from Eq. (18), p.27).
"With high probability, the test at λ+ passes and the test at λ− fails."

There is an absolute `c₀` such that for every `c ≥ c₀` there are `a > 0` and `n₀` with: for every
`δ ∈ (0, 1/2)`, `n ≥ n₀`, `1 ≤ k < n`, metric `d`, aspect-ratio bound `aspect(d) ≤ Δ`, adversary,
LP routine returning optimal solutions, `ε ∈ (0, 1]` and offline routine with guarantee `(3 + ε)`:
with probability at least `1 − n^{−a}` over the corruption set and the (independent) randomness of
the two tests, the test at `λ₊ = Δd₀/k` passes and the test at `λ₋ = d₀/(2Ck∆)` fails, where
`d₀ = d(u, v)`, `C = 3000`, and passing means not aborting with total radius at most `Ckλ`.

**Formalization Note.** `u, v` are the points `0, 1`. -/
theorem lemma_3_36 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → ∀ Δ : ℝ, aspectRatio d ≤ Δ →
    ∀ adv : Adversary n, ∀ sel : LPSelector n, SelectsOptimal sel →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ off : OfflineRoutine n k, GoodOffline d ε off →
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        jointProb δ (fun C =>
            (testLaw c δ k (lamPlus d k Δ) sel off d (weakDist d C adv)).bind (fun tp =>
              (testLaw c δ k (lamMinus d k Δ) sel off d (weakDist d C adv)).map
                (fun tm => (tp, tm))))
          (fun _ p => passes (lamPlus d k Δ) p.1 ∧ ¬ passes (lamMinus d k Δ) p.2) := by sorry

end WeakStrongMSR
