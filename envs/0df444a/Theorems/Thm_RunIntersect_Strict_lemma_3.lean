-- Prove2me | Theorems.Thm_RunIntersect_Strict_lemma_3
-- name    : RunIntersect.Strict.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:39.94126+00:00
-- url     : https://prove2.me/theorems/a70b7fe3-1341-4824-8b7a-33676e7c5689
-- title:
--   Lemma 3, p. 1018 — a β-cycle of a subhypergraph G_{V′} gives a β-cycle of G of the same length
-- statement:
--   Let $G=(V,E)$ be a hypergraph and $V'\subseteq V$. If the subhypergraph $G_{V'}$ contains a β-cycle of length $t$, then $G$ contains a β-cycle of length $t$. In particular,
--   $$G\ \text{β-acyclic}\ \Longrightarrow\ G_{V'}\ \text{β-acyclic}.$$
--
--   The lemma lets a short β-cycle found in an induced subhypergraph be transported back to $G$; it is used in the proof of Proposition 5 to show that the subhypergraph induced by a shortest β-cycle has a very rigid shape.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1018, Lemma 3

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Lemma 3, p. 1018: a β-cycle of length `t` of the subhypergraph `G_W` (`W ⊆ V`) gives a β-cycle of
length `t` of `G`; in particular `G_W` is β-acyclic when `G` is. -/
theorem lemma_3 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (W : Finset α)
    (hW : W ⊆ G.V) :
    (∀ (t : ℕ) (v : Fin t → α) (e : Fin t → Finset α), IsBetaCycle (subHg G W) t v e →
        ∃ (v' : Fin t → α) (e' : Fin t → Finset α), IsBetaCycle G t v' e') ∧
      (IsBetaAcyclic G → IsBetaAcyclic (subHg G W)) := by sorry

end RunIntersect.Strict
