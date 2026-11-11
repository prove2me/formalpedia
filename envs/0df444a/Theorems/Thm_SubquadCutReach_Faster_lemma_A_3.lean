-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_A_3
-- name    : SubquadCutReach.Faster.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:36.406564+00:00
-- url     : https://prove2.me/theorems/efcbeffd-30ab-4de5-8119-551956e7f255
-- title:
--   Lemma A.3 — Faster averaging
-- statement:
--   Let $H$ have $n$ vertices and let $b^*$ be a feasible target. For every integer $1\le T\le n$, a uniform deterministic program executes the specified two-loss-evaluation recurrence and returns its average of trial fractional rules $\bar z$.
--
--   $$Q\le CnT\log(n+2),\qquad \|b_{\bar z}-b^*\|_1\le Cn^2/T.$$
--
--   Every increasing-pair probability $(1+\bar z(u,v))/2$ has numerator and positive denominator with at most $K(\lfloor\log_2(n+2)\rfloor+1)$ binary digits. The absolute constants precede all inputs. Precision is fixed to $6+5(\lfloor\log_2 n\rfloor+1)$ coefficient digits. This controls both query cost and the finite arithmetic representation; it does not assume estimates or their accuracy as free inputs.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
--   - encoding: a sufficiently strong O(log n)-bit imbalance approximation → signed coefficient truncation with B=6+5(floor log₂ n+1); reason: 2^(-B) ≤ 1/(64 n^5) for n≥1, so per-vertex error is at most 1/(64 n^4); two loss evaluations remain charged and both updates start at the persistent state
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 21, Lemma A.3 (PDF p. 23)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_A_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧ ∃ P : Program,
      Admissible P ∧ Deterministic P ∧
      ∀ (n T : ℕ) (H : SimpleGraph (Fin n)) (b : Fin n → ℤ),
        1 ≤ T → T ≤ n → Feasible H b →
        RunsWithin P (cut H) (targetInput b T)
          (fun m => outputFrac n m = average H b T ∧ ValidFractional (outputFrac n m) ∧
            l1 (fun v => fractionalImbalance H (outputFrac n m) v - b v) ≤ C*(n:ℝ)^2/T ∧
            ∀ u v, u < v → RationalBits (K*(Nat.log 2 (n+2)+1))
              ((1+outputFrac n m u v)/2))
          (C*n*T*L n) := by sorry

end SubquadCutReach.Faster
