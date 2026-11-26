-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_lemma_3_9
-- name    : Scott1972.ContinuousLattice.lemma_3_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:13.622699+00:00
-- url     : https://prove2.me/theorems/48991c3c-e6d7-4b3a-bb37-514db365db4f
-- title:
--   Continuous Lattice: lemma 3 9
-- statement:
--   **Scott 1972, Lemma 3.9.** With `e : X → Y` a subspace embedding and `i, j : D ⇄ D'` a
--   projection on the range, if continuous `f : X → D` and `g : X → D'` satisfy `f = j ∘ g`, then the
--   maximal extensions (Proposition 3.8) satisfy `f̄ = j ∘ ḡ`.
--
--   The proof is Scott's, recast through the faithful `scottExtend`:
--   * `j ∘ ḡ ⊑ f̄`: `j ∘ ḡ` is a continuous solution of `(j ∘ ḡ) ∘ e = j ∘ g = f`, so maximality of
--     `f̄` (`scottExtend_maximal`) gives the bound;
--   * `i ∘ f̄ ⊑ ḡ`: `(i ∘ f̄) ∘ e = i ∘ f = i ∘ j ∘ g ⊑ g` (since `i ∘ j ⊑ id`), so the *sub*-solution
--     maximality of `ḡ` (`scottExtend_maximal_le`, the remark after 3.8) gives the bound;
--   * combining: `f̄ = j ∘ i ∘ f̄ ⊑ j ∘ ḡ ⊑ f̄` (using `j ∘ i = id` and monotonicity of `j`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L365-L404
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L365-L404

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X Y D D' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompleteLattice D] [CompleteLattice D']

theorem Scott1972.ContinuousLattice.lemma_3_9 (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    (P : IsContinuousLatticeProjection D D') (e : X → Y) (he : IsEmbedding e)
    {f : X → D} {g : X → D'} (hf : @Continuous X D _ scottTopologicalSpace f)
    (hg : @Continuous X D' _ scottTopologicalSpace g)
    (hfg : ∀ x, f x = (P.retr : D' → D) (g x)) (y : Y) :
    scottExtend e f y = (P.retr : D' → D) (scottExtend e g y) := by sorry
