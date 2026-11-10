-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_theorem_2_3
-- name    : SteinerShortcuts.Main.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:34:22.992168+00:00
-- url     : https://prove2.me/theorems/fd4e1d8f-9efa-422d-8e51-b98bb34c4fc9
-- title:
--   Theorem 2.3 — Steiner shortcut lower bound template
-- statement:
--   Let $G=(V,E)$ be any finite layered DAG with a finite critical family $\mathcal P$, every member of length $D$, satisfying uniqueness (P1) and compatible-pair overlap (P2). For every finite Steiner shortcut $G^+=(V\sqcup W,E\cup E^+)$, there is a non-Steiner shortcut $G'=(V,E\cup E')$ satisfying
--   $$
--   |E'|\le |E^+|,\qquad
--   \forall P\in\mathcal P,\quad d_{G'}(s(P),t(P))\le d_{G^+}(s(P),t(P)).
--   $$
--   The conclusion explicitly requires preservation of original reachability in both directions. The paths have equal length but may start and finish at different layers, as the paper's application on page 23 requires. No structural restriction is imposed on the Steiner augmentation.
--
--   Differences from the source:
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
--   - encoding: finite layered DAGs and Steiner shortcuttings → Mathlib Digraph, finite vertex types, explicit layer and reachability iff predicates, and imported extended-natural hop distances; reason: this preserves the original augmentation domain; all compared critical endpoint distances are finite
--   - reading: the template is stated for layered critical paths and used on arbitrary-layer equal-length subpaths on p.23 → paths of equal length D at arbitrary layers; reason: p.23 explicitly says the Appendix A proof does not require common starting and ending layers
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 5–6, Theorem 2.3; arbitrary-layer application on p.23 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Graphs

namespace SteinerShortcuts.Main

theorem theorem_2_3 {V W : Type} [Fintype V] [Fintype W]
    (G : Digraph V) (layer : V → ℕ) (hl : IsLayered G layer)
    (paths : Finset (Route V)) (D : ℕ) (hlen : ∀ P ∈ paths, P.length = D)
    (hp1 : P1 G paths) (hp2 : P2 G paths)
    (extra : Finset ((V ⊕ W) × (V ⊕ W))) (he : IsSteinerShortcut G extra) :
    ∃ nonSteiner : Finset (V × V), IsShortcut G nonSteiner ∧ nonSteiner.card ≤ extra.card ∧
      ∀ P ∈ paths, PredAdvice.dist (addEdges G nonSteiner) P.start P.finish ≤
        PredAdvice.dist (augment G extra) (Sum.inl P.start) (Sum.inl P.finish) := by sorry

end SteinerShortcuts.Main
