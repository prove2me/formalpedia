-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_3_5
-- name    : SubquadCutReach.Faster.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:52.323284+00:00
-- url     : https://prove2.me/theorems/4d266d70-71cf-4acd-b387-e840d6c13b60
-- title:
--   Lemma 3.5 — Directed reachability via orientation rules
-- statement:
--   Suppose a uniform zero-error program constructs a rule matching every feasible target on every hidden simple graph, with expected query count at most $Q(n)$. There is a uniform zero-error directed-reachability program with
--
--   $$\mathbb E Q_{\rm reach}\le C\bigl(n\log(n+2)+Q(n)\bigr).$$
--
--   The same composed program transfers every polynomial tail profile: a matching-program bound $q(n)$ with failure at most $n^{-c}$ gives reachability bound $C(n\log(n+2)+q(n))$ with that same failure probability. If the matching program halts on every tape within $Q(n)$ queries, the same composed program halts on every tape within $C(n\log(n+2)+Q(n))$ queries. A deterministic matching program gives a deterministic reachability program. The matching target is feasible existentially; its realizing orientation is never supplied.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
--   - generalization: a Q(n)-query orientation-rule subroutine and O(n log n+Q(n)) reduction → explicit worst-case transfer and preservation of determinism, together with expectation and every polynomial cost-tail profile for zero-error subroutines; reason: the source proof adds deterministic O(n log n) overhead and simulates each undirected query by two directed queries; the worst-case and deterministic clauses explicitly retain the source reduction
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 7, Lemma 3.5 (PDF p. 9)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

/-- Transfer of worst-case bounds, expectation and every tail profile for the same program. -/
theorem lemma_3_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ → ℝ), (∀ n, 0 ≤ Q n) →
      ∀ P : Program, Admissible P → (∀ i : MatchCase, MatchCorrect P i) →
        (∀ i : MatchCase, expected P (cut i.H) (targetInput i.b 0) ≤ ENNReal.ofReal (Q i.n)) →
        ∃ R : Program, Admissible R ∧ (∀ i : ReachCase, ReachCorrect R i) ∧
          (∀ i : ReachCase, expected R (outCut i.G) (reachInput i) ≤
            ENNReal.ofReal (C*(i.n*L i.n+Q i.n))) ∧
          (Deterministic P → Deterministic R) ∧
          ((∀ i : MatchCase, RunsWithin P (cut i.H) (targetInput i.b 0)
            (fun m => imbalance (induced i.H (outputRule i.n m)) = i.b) (Q i.n)) →
            ∀ i : ReachCase, RunsWithin R (outCut i.G) (reachInput i)
              (fun m => (m 0 = 0 ∨ m 0 = 1) ∧ (m 0 = 1 ↔ reachable i.G i.s i.t))
              (C*(i.n*L i.n+Q i.n))) ∧
          ∀ (c : ℝ) (q : ℕ → ℝ), 0 < c →
            (∀ i : MatchCase, Tail P (cut i.H) (targetInput i.b 0) (q i.n) c) →
            ∀ i : ReachCase, Tail R (outCut i.G) (reachInput i)
              (C*(i.n*L i.n+q i.n)) c := by sorry

end SubquadCutReach.Faster
