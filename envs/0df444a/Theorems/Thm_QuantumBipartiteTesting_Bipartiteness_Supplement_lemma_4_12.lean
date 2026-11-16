-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_12
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:19:36.161902+00:00
-- url     : https://prove2.me/theorems/195e7c9c-01d1-4fb4-86bf-6ee54b37a820
-- title:
--   Lemma 4.12 — Once-per-edge subdivisions preserve positive vertex expansion
-- statement:
--   For every $\rho>0$ there is $\alpha>0$, depending only on $\rho$, such that every simple $m$-vertex graph $G$ of maximum degree at most four satisfying
--   $$|e_G(U,U^c)|\ge\rho\min\{|U|,m-|U|\}\quad\text{for every }U$$
--   has the following property: subdividing any set of at most $m/4$ distinct edges, once per selected edge, gives a graph $G'$ with vertex expansion at least $\alpha$. The constant precedes the graph size, graph and subdivision set. This preserves the YES promise for arbitrary-size adjustments, and is not restricted to replacement graphs.
--
--   Differences from the source:
--   - encoding: an m-vertex simple graph and r at most m/4 once-subdivided edges → Fin m and a selected subset T of original edges with 4 card(T) at most m, labeled by any bijection; reason: the construction represents every permitted subdivision and excludes repeated subdivisions
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.12, printed page = PDF page 26; proof pp.39–40

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_12 (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ α : ℝ, 0 < α ∧ ∀ m : ℕ, ∀ G : Finset (Edge m),
      IsGraph G → DegreeBound 4 G → EdgeExpander ρ G →
      ∀ T : Finset (Edge m), T ⊆ G → 4*T.card ≤ m →
      ∀ idx : {x // x ∈ T} ≃ Fin T.card,
        VertexExpander α (Subdivision G T idx) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
