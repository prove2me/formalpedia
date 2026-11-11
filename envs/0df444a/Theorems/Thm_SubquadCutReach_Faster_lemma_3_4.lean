-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_3_4
-- name    : SubquadCutReach.Faster.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:28.18546+00:00
-- url     : https://prove2.me/theorems/a4c0b1ae-d562-431b-aa79-ad481e6858e8
-- title:
--   Lemma 3.4 — Graph search under an orientation rule
-- statement:
--   Let $H$ be a hidden simple graph and $\mathcal D$ a known rule evaluable on all pairs. A uniform deterministic program decides whether $t$ is reachable from $s$ in its induced orientation $D$, using only cut queries to $H$.
--
--   $$Q\le Cn\log(n+2).$$
--
--   The constant and program precede the graph, rule and terminal inputs. The returned bit is an exact reachability answer. This makes a computed orientation rule usable without recovering all graph edges.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 7, Lemma 3.4 (PDF p. 9)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_3_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧ Deterministic P ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (D : Rule n) (s t : Fin n),
        RunsWithin P (cut H) (searchInput D s t)
          (fun m => (m 0 = 0 ∨ m 0 = 1) ∧ (m 0 = 1 ↔ reachable (induced H D) s t))
          (C * n * L n) := by sorry

end SubquadCutReach.Faster
