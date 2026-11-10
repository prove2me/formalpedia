-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_equation_11
-- name    : SteinerShortcuts.Main.equation_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:26.822551+00:00
-- url     : https://prove2.me/theorems/447c46e9-bc0a-4a1c-b792-c2e8ec39e8db
-- title:
--   §3.2, eq. (11) — uniform construction sizes
-- statement:
--   For every even $L\ge4$ and every prime $q\in[L,2L]$, let $S,V,C,E,\mathcal P$ be the actual source box, vertex set, direction set, edge set and critical-path family of §3.2. There are positive constants independent of both $L$ and $q$ such that all comparisons in
--   $$
--   n=\Theta(L|S|)=\Theta(L^{56}),\qquad
--   m=\Theta(L|S||C|)=\Theta(L^{57}),\qquad
--   |\mathcal P|=|S||C|^2=\Theta(m)
--   $$
--   hold in both directions. The same statement includes the adjoining source facts that every computed critical path stays in $G$ and that distinct triples $(s,a,b)$ give distinct paths. Counts are cardinalities of actual tuples, edges and sequences, not certificate fields.
--
--   **Formalization Note** A single positive lower constant $c$ and upper constant $C$ bound the five ratios simultaneously. Taking their minimum and maximum is equivalent to allowing separate constants.
--
--   Differences from the source:
--   - reading: the Θ notation in eq. (11) → existential positive constants before every admissible L and q, with both inequalities for each of the five ratios; reason: the proof gives uniform box bounds; finitely many initial even sizes are absorbed into the same constants
--   - encoding: the cardinality identity and the preceding containment/distinctness assertions → computed finite-set cardinalities, path validity, vertex containment and injectivity of the source-and-label map; reason: this exposes the adjoining assertions needed for the identity, without defining paths to be distinct or contained
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 22, §3.2, eq. (11) (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main

/-- All constants precede L and q; counts are counts of tuples, edges, and routes. -/
theorem equation_11 :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ L q : ℕ, Admissible L q →
      (c * ((L * (sources L q).card : ℕ) : ℝ) ≤ ((vertices L q).card : ℝ) ∧
        ((vertices L q).card : ℝ) ≤ C * ((L * (sources L q).card : ℕ) : ℝ)) ∧
      (c * (L : ℝ)^56 ≤ ((vertices L q).card : ℝ) ∧
        ((vertices L q).card : ℝ) ≤ C * (L : ℝ)^56) ∧
      (c * ((L * (sources L q).card * (directions q).card : ℕ) : ℝ) ≤
          ((constructionEdges L q).card : ℝ) ∧
        ((constructionEdges L q).card : ℝ) ≤
          C * ((L * (sources L q).card * (directions q).card : ℕ) : ℝ)) ∧
      (c * (L : ℝ)^57 ≤ ((constructionEdges L q).card : ℝ) ∧
        ((constructionEdges L q).card : ℝ) ≤ C * (L : ℝ)^57) ∧
      (criticalPaths L q).card = (sources L q).card * (directions q).card^2 ∧
      (c * ((constructionEdges L q).card : ℝ) ≤ ((criticalPaths L q).card : ℝ) ∧
        ((criticalPaths L q).card : ℝ) ≤ C * ((constructionEdges L q).card : ℝ)) ∧
      (∀ P ∈ criticalPaths L q, IsPath (construction L q) P ∧
        ∀ v ∈ P.vertices, v ∈ vertices L q) ∧
      (Function.Injective (fun sab : ↥(sources L q) × (Fin q × Fin q) =>
        critical L q sab.1.val sab.2.1 sab.2.2)) := by sorry

end SteinerShortcuts.Main
