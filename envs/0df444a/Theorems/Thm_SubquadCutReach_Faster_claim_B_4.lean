-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_claim_B_4
-- name    : SubquadCutReach.Faster.claim_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:59:32.572199+00:00
-- url     : https://prove2.me/theorems/a97c1077-7809-48eb-9f05-1b403648dd14
-- title:
--   Claim B.4 — Reserve succeeds
-- statement:
--   Use the actual reserve from the residual forest union plus independently sampled potential edges, and independently orient unreserved pairs with fair directions. For every fixed $c>0$, there is a positive reserve coefficient $a$ and threshold $N_c$, independent of the graph and the valid residual forest sequence, such that
--
--   $$\Pr\left\{\exists S\subseteq V:\left|\sum_{v\in S}b_{D_0}(v)\right|>C_R(S)\right\}\le n^{-c}\qquad(n\ge N_c).$$
--
--   Sampling probability is capped at one. The event controls all cuts simultaneously. Endpoint contributions of one edge are coupled, while distinct pair samples are independent. This is a success estimate for one reserve trial, not an assumption of correctness of a randomized output.
--
--   Differences from the source:
--   - encoding: a Θ(log n/√k) independent additional reserve and high probability → rate min(1,a log n/√k), independent uniform coordinates, and failure at most n^(-c) for every fixed c after an input-independent threshold; reason: the proof on printed p.26 expressly gives arbitrary fixed c by setting constants; directions of distinct pairs are fair and independent
--   - reading: F built from 10k log n forests with the base of log unspecified → ceil(10k Real.log n) forests; reason: the base is not stated; the natural logarithm gives the smaller reserve, so it is the stronger reading (the base of the sampling rate is absorbed in the existential coefficient a)
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 26, Claim B.4 (PDF p. 28)

import Definitions.Def_SubquadCutReach_Faster_Reserve

set_option autoImplicit false
open MeasureTheory

namespace SubquadCutReach.Faster

theorem claim_B_4 :
    ∀ c : ℝ, 0 < c → ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ J : SimpleGraph (Fin n),
        ∀ Fs : ℕ → Finset (Fin n × Fin n), ForestRun J Fs (forestRounds n) →
          reserveLaw n {ω | ¬ CompletionCondition J
            (reserve J (forestUnion Fs (forestRounds n)) a ω) (randomDirection ω)} ≤
              ENNReal.ofReal ((n:ℝ)^(-c)) := by sorry

end SubquadCutReach.Faster
