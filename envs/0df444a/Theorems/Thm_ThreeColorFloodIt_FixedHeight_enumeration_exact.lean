-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_enumeration_exact
-- name    : ThreeColorFloodIt.FixedHeight.enumeration_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:40.774321+00:00
-- url     : https://prove2.me/theorems/0ba42735-f206-41ec-912f-df835921bf8d
-- title:
--   Lemma 14 — Exact direct enumeration and polynomial generation
-- statement:
--   For a connected window graph $G[B]$ with $s$ named vertices and target coloring $f$, the concrete skeleton recursion followed by alternating-chain expansion generates exactly the local templates with at most $M$ nodes, up to rooted tree isomorphism preserving colors and named owners. Both generation directions are asserted.
--
--   One deterministic generator takes the window, its colors and the variable budget as input; for each fixed $s$ there are constants $c_s,e_s$ such that its full encoded output is written within
--   $$c_s(M+1)^{e_s}\text{ machine steps}.$$
--   This includes the zero-budget empty output and all path nodes. Ordered child representations may repeat an isomorphism class, which does not change exactness and only changes a factor depending on $s$. The generator is defined by the recursion, not by enumerating a predicate of valid templates.
--
--   Differences from the source:
--   - encoding: exact enumeration of local templates in polynomial time for fixed s → two isomorphism-preserving coverage directions and a uniform finite machine writing the explicit recursive generator list; reason: ordered representatives and repetitions change no generated template and only a window-size factor; time includes output writing
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 10 (PDF 11), Lemma 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_enumeration

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem enumeration_exact :
    (∀ (s M : ℕ) (G : SimpleGraph (Fin s)) (f : Fin s → Fin 3),
      ConnectedSet G Set.univ →
      (∀ t ∈ generateTemplates G f M, ∃ K : TreeData (Fin s) (Fin 3),
        LocalTemplate G f K ∧ K.tree.size ≤ M ∧ Flattens K t) ∧
      (∀ K : TreeData (Fin s) (Fin 3), LocalTemplate G f K → K.tree.size ≤ M →
        ∃ t ∈ generateTemplates G f M, Flattens K t)) ∧
    (∃ A : IntMul.MultitapeTM, ∀ s : ℕ, ∃ c e : ℕ, 0 < c ∧
      ∀ (M : ℕ) (G : SimpleGraph (Fin s)) (f : Fin s → Fin 3),
        ConnectedSet G Set.univ → ∃ t : ℕ, t ≤ c * (M + 1) ^ e ∧
          A.HaltsWithOutputW (windowInput G f M) t (generatedCode G f M)) := by sorry

end ThreeColorFloodIt.FixedHeight
