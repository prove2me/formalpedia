-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_assign_balanced
-- name    : PigeonholeDesign.MultiDim.assign_balanced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:36:27.181952+00:00
-- url     : https://prove2.me/theorems/1771d1db-2f6e-4d37-8aa0-9aae76964ea1
-- title:
--   p. 16 — Step 1 makes every run of a pigeonhole design put exactly T/2 subjects in each group
-- statement:
--   Let $T$ be even. For every partition of the covariate space into pigeonholes, every arrival sequence $x_1,\dots,x_T$ and every outcome of the tie-breaking coins, the pigeonhole design (Definition 3) assigns exactly $T/2$ subjects to control and exactly $T/2$ to treatment:
--   $$|A|=|B|=\frac T2 .$$
--
--   This is the role of Step 1 of the design. It makes the discrepancy $d_{A,B}$ of every run a genuine minimum-weight perfect matching.
--
--   **Formalization Note** The pigeonhole partition is given as an arbitrary map `hole` from the covariate space to a type of labels with decidable equality; its fibres are the pigeonholes. The statement is about every coin vector, not on average. It guarantees that the junk value $0$ of the discrepancy of an unbalanced split never occurs for this design.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 16, remark after Definition 3

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting

namespace PigeonholeDesign.MultiDim

theorem assign_balanced {E ι : Type*} [DecidableEq ι] (T : ℕ) (hT : Even T) (hole : E → ι)
    (x : Fin T → E) (coin : Fin T → Bool) :
    (Finset.univ.filter (fun t => PigeonholeDesign.Lower.assign hole x coin t = false)).card = T / 2 ∧
      (Finset.univ.filter (fun t => PigeonholeDesign.Lower.assign hole x coin t = true)).card = T / 2 := by sorry

end PigeonholeDesign.MultiDim
