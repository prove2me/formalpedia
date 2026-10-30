-- Prove2me | Theorems.Thm_RobustDP_ChiSquareAudit_lemma5_full
-- name    : RobustDP.ChiSquareAudit.lemma5_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:45:42.258463+00:00
-- url     : https://prove2.me/theorems/8c612b6b-4917-4ab1-931c-f8034aa70ba8
-- title:
--   Lemma 5 — attained robust expectation and exact optimizer in sorting time
-- statement:
--   Let $S$ be any finite state set, $q:S\to\mathbb R$ any probability vector, $v:S\to\mathbb R$ arbitrary, and $t\ge0$. Define $P$ by the support-aware chi-square constraint: $p$ is a probability vector, vanishes wherever $q$ vanishes, and its sum of squared deviations divided by $q$ over positive support is at most $t$. Expectations and variances are weighted by $q$, with variance centred at the weighted mean.
--
--   For any enumeration of $S$, the single fixed exact-arithmetic program returns a real value $V$, a threshold $\alpha$ and a materialized nonnegative vector $\mu(s)=\max(v(s)-\alpha,0)$ such that
--   $$V=\min_{p\in P}\sum_s p(s)v(s)
--   =\max_{\nu\ge0}\left(E^q[v-\nu]-\sqrt{t\operatorname{Var}^q[v-\nu]}\right)
--   =E^q[v-\mu]-\sqrt{t\operatorname{Var}^q[v-\mu]}.$$
--   Both extrema are attained. The theorem also identifies $P$ with the extended nonnegative-divergence ball, using $0/0=0$ and nonzero divided by zero equal to infinity, and proves that it equals the published ordinary chi-square set when every $q(s)>0$.
--
--   The operation count is obtained from the same execution that constructs the output. For $n=|S|$, it is bounded by
--   $$512(n+1)\bigl(1+\lceil\log_2(n+1)\rceil\bigr).$$
--   Moreover there are a positive constant $C$ and a threshold $n_0=0$, chosen before every state space and all input data, giving that same bound shape with $C$ in place of 512 for every $n\ge n_0$. This is exact $O(n\log n)$ arithmetic work for $n\ge2$, and also covers singleton support. The penalty constant is exactly 1.
--
--   This is the whole Lemma 5, including the computational clause absent from the already Proved value-only reference. No accuracy parameter, small-radius condition or variance nondegeneracy assumption is imposed. **Formalization Note** Addition, subtraction, multiplication, guarded division, comparison, nonnegative square root, coordinate access and ordinary structural/index work are charged. This is an exact-real operation model, not bit complexity. The numerical 512 follows from the defined program's count and is not a source constant.
--
--   Differences from the source:
--   - generalization: (46) divides by q(s) and is defined for positive centres; q=(1,0), p=q already contains undefined 0/0 → all probability centres are admitted by forcing p(s)=0 at zero q(s), summing only on positive support, and equating this set with the extended-divergence ball; reason: every strictly positive-centre instance specializes exactly to the printed set; the report does not say to delete empirical zero-count states
--   - encoding: an arbitrary finite S and O(|S| log |S|) complexity of solving (48) → transport through any Fin(card S) equivalence, the fixed program solve, actual output array, and uniform cost bound 512(n+1)(1+ceil(log2(n+1))) with constants before all spaces and data; reason: enumeration changes no mathematical instance; unit-cost exact real arithmetic, guarded square roots and structural work make the operation convention explicit, include n=1 and implement the source's asymptotic claim without attributing 512 to it
-- source:
--   G. Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07, revised May 4, 2004, p. 18–19, Lemma 5, (46)–(48), including optimizer computation and the sorting-time conclusion

import Mathlib
import Definitions.Def_RobustDP_ChiSquareAudit_Program

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

/-- Whole Lemma 5, pp.18-19: exact attained primal/dual value and an explicit
maximizing vector computed by the fixed program `solve` in sorting time.
Constants precede every finite state space and every real input. Zero-centre
coordinates use the extended-divergence convention, agreeing with (46) wherever
the printed division is defined. The numerical 512 is an implementation bound,
not a constant printed in Iyengar's report. -/
theorem lemma5_full :
    ∃ C n₀ : ℕ, 0 < C ∧ n₀ = 0 ∧
    ∀ {S : Type} [Fintype S] (q : S → ℝ), q ∈ stdSimplex ℝ S →
      ∀ (t : ℝ), 0 ≤ t → ∀ (v : S → ℝ)
        (e : Fin (Fintype.card S) ≃ S),
      let n := Fintype.card S
      let execution := solve n (q ∘ e) t (v ∘ e)
      let out := execution.value
      let μ : S → ℝ := fun s => answerMultiplier (n := n) out (e.symm s)
      out.multiplier.size = n ∧
      μ = clippedMultiplier v out.best.alpha ∧ (∀ s, 0 ≤ μ s) ∧
      out.best.val = dualObj q t v μ ∧
      IsLeast ((fun p => expect p v) '' supportBall q t) out.best.val ∧
      IsGreatest ((fun ν => dualObj q t v ν) '' {ν : S → ℝ | 0 ≤ ν}) out.best.val ∧
      (∀ p : S → ℝ, p ∈ supportBall q t ↔
        p ∈ stdSimplex ℝ S ∧ extendedDistance p q ≤ ENNReal.ofReal t) ∧
      ((∀ s, 0 < q s) → supportBall q t = chiSqSet q t) ∧
      execution.steps ≤ 512 * (n + 1) * (1 + sortingLevels n) ∧
      (n₀ ≤ n → execution.steps ≤ C * (n + 1) * (1 + sortingLevels n)) := by sorry

end RobustDP.ChiSquareAudit
