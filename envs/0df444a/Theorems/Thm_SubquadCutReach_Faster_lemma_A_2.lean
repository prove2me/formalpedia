-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_A_2
-- name    : SubquadCutReach.Faster.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:59:17.820454+00:00
-- url     : https://prove2.me/theorems/bc11dd37-b92d-4c34-aca0-3d926a39d5a8
-- title:
--   Theorem A.2 — Optimistic mirror descent regret
-- statement:
--   Let $B=[-1,1]^d$ with $d\le2n^2$, horizon $1\le T\le n$, step size $\eta=1/8$, and initial state zero. Use the specified optimistic projected updates, both starting at $v_t$. Losses and predictions may be arbitrary adaptive sequences. If in every round
--
--   $$\|\ell_t-\widehat\ell_t\|_2\le2\|v_t^+-v_t\|_2+2/n^2,$$
--
--   then one absolute positive constant satisfies $\operatorname{Reg}_T(u)\le Cn^2$ simultaneously for every $u\in B$. Regret is the sum of inner products with the trial state minus the comparator. This is the analytic estimate for faster averaging; both norms in its hypothesis are unsquared.
--
--   Differences from the source:
--   - encoding: one-based optimistic rounds on a Euclidean box with an O(n²) conclusion → zero-based finite sums and an absolute positive C before n,d,T,losses and comparators; reason: the horizon and all projected updates, unsquared hypothesis and simultaneous comparators are unchanged
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 20, Theorem A.2 (PDF p. 22)

import Definitions.Def_SubquadCutReach_Faster_Averaging

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_A_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d T : ℕ), 1 ≤ T → T ≤ n → d ≤ 2*n^2 →
      ∀ loss hint : ℕ → Fin d → ℝ,
        (∀ t < T, l2 (fun i => loss t i - hint t i) ≤
          2*l2 (fun i => omdTrial loss hint t i - omdState loss hint t i) + 2/(n:ℝ)^2) →
        ∀ u : Fin d → ℝ, (∀ i, -1 ≤ u i ∧ u i ≤ 1) →
          regret loss hint T u ≤ C*(n:ℝ)^2 := by sorry

end SubquadCutReach.Faster
