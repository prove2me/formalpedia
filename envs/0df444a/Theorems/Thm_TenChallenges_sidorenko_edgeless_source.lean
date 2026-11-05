-- Prove2me | Theorems.Thm_TenChallenges_sidorenko_edgeless_source
-- name    : TenChallenges.sidorenko_edgeless_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:30.088346+00:00
-- url     : https://prove2.me/theorems/d8e107d8-fb99-4b49-bc44-63eee972bdf7
-- title:
--   Sidorenko conjecture: Edgeless source graphs
-- statement:
--   Every finite edgeless source graph satisfies Sidorenko’s inequality for every finite nonempty target graph.
-- source:
--   Elementary special case / supporting lemma for Challenge 04. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_TenChallenges_Challenge_04
import Mathlib.SetTheory.Cardinal.Finite
open SimpleGraph

theorem TenChallenges.sidorenko_edgeless_source {W V : Type*} [Fintype W] [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : SidorenkoFor (⊥ : SimpleGraph W) G := by sorry
