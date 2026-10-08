-- Prove2me | Theorems.Thm_StrongPerfectGraph_EvenPrism_prism_paths_same_parity
-- name    : StrongPerfectGraph.EvenPrism.prism_paths_same_parity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:27:14.315957+00:00
-- url     : https://prove2.me/theorems/2b8521b8-a826-4a02-83a5-d82ca7dd3c7c
-- title:
--   7.2 — the three prism paths have the same parity
-- statement:
--   Let $R_1,R_2,R_3$ be the three paths of a prism in a Berge graph $G$. Then
--
--   $$|E(R_i)|\equiv |E(R_j)|\pmod 2\qquad(1\le i,j\le 3).$$
--
--   This is the parity fact used to distinguish even and odd prisms.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 93, 7.2

import Definitions.Def_StrongPerfectGraph_EvenPrism_Prism

namespace StrongPerfectGraph.EvenPrism

theorem prism_paths_same_parity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (hR : IsPrism G a b R) :
    ∀ i j, Even ((R i).length - 1) ↔ Even ((R j).length - 1) := by sorry

end StrongPerfectGraph.EvenPrism
