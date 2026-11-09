-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_seed_doubling_vertex
-- name    : ThinningSprinkling306.ToughCycles.seed_doubling_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:13.227769+00:00
-- url     : https://prove2.me/theorems/8eee8304-4aeb-4397-94a0-8dc167424c48
-- title:
--   Lemma 2.1 — one seed witnesses doubling at every genuine growth
-- statement:
--   Let $G$ be a finite simple graph, and let $U_0,\ldots,U_\ell$ be arbitrary deterministic vertex subsets. Put $W_i=\bigcup_{j=0}^i U_j$, and let $C_i(v)$ be the component of $v$ in $G[W_i]$, empty when $v\notin W_i$. If $C$ is a component of $G$ meeting $U_0$, then one vertex $v\in C\cap U_0$ satisfies, for every $i<\ell$,
--   $$
--   C_i(v)\cap U_0=C_{i+1}(v)\cap U_0
--   \quad\text{or}\quad
--   2|C_i(v)\cap U_0|\le |C_{i+1}(v)\cap U_0|.
--   $$
--   The same seed works at every stage. This is a deterministic statement and assumes no sampling independence.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: the finite list U_0,…,U_ell and 0≤i≤ell−1 → a natural-indexed sequence inspected only through ell, with i<ell; reason: every finite list extends to such a sequence and the ell=0 case has no stage condition
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 6, Lemma 2.1 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling

namespace ThinningSprinkling306.ToughCycles

/-- Lemma 2.1, printed p. 6 (PDF p. 8). -/
theorem seed_doubling_vertex {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ)
    (U : ℕ → Finset (Fin n)) (C : Finset (Fin n))
    (hC : C ∈ components G Finset.univ) (hseed : (C ∩ U 0).Nonempty) :
    ∃ v ∈ C ∩ U 0, ∀ i : ℕ, i < ℓ →
      component G (exposed U i) v ∩ U 0 = component G (exposed U (i + 1)) v ∩ U 0 ∨
      2 * (component G (exposed U i) v ∩ U 0).card ≤
        (component G (exposed U (i + 1)) v ∩ U 0).card := by sorry

end ThinningSprinkling306.ToughCycles
