-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_lemma_2_4
-- name    : SteinerShortcuts.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:34:43.105203+00:00
-- url     : https://prove2.me/theorems/f21ce0ae-9751-49d3-bb4c-431d555fdcb5
-- title:
--   Lemma 2.4 — a common vertex for a compatible family
-- statement:
--   Let $G$ be a finite layered DAG with critical family $\mathcal P$ satisfying (P1) and (P2). For every nonempty compatible subfamily $\mathcal F\subseteq\mathcal P$,
--   $$
--   \exists v\in V,\qquad v\in P\quad\text{for every }P\in\mathcal F.
--   $$
--   The common vertex belongs to the original graph. This turns compatible-pair overlap into overlap of the entire family, including a singleton family.
--
--   Differences from the source:
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
--   - encoding: layered DAG and finite compatible subfamily → a natural-number layer map increasing by one along each edge, and Finset families; reason: this states the section setup explicitly; the lemma uses no common-end-layer or equal-length assumption
--   - generalization: critical paths in the common-end-layer setup of Section 2.1 → finite families of paths at arbitrary layers, without an equal-length requirement; reason: the proof uses only uniqueness and compatible-pair overlap to obtain intersecting intervals along P₀; it never uses common endpoints layers or lengths, as also noted for subpath applications on pp.23 and 27
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 6, Lemma 2.4 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Graphs

namespace SteinerShortcuts.Main

theorem lemma_2_4 {V : Type} [Fintype V] (G : Digraph V) (layer : V → ℕ)
    (hl : IsLayered G layer) (paths : Finset (Route V)) (hp1 : P1 G paths) (hp2 : P2 G paths)
    (F : Finset (Route V)) (hf : F ⊆ paths) (hne : F.Nonempty) (hc : CompatibleFamily G F) :
    ∃ v : V, ∀ P ∈ F, v ∈ P.vertices := by sorry

end SteinerShortcuts.Main
