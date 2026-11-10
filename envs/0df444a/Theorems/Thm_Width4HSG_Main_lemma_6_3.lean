-- Prove2me | Theorems.Thm_Width4HSG_Main_lemma_6_3
-- name    : Width4HSG.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:20:25.588169+00:00
-- url     : https://prove2.me/theorems/0185c87d-5ad0-4e9e-b60c-dcf5c6485f52
-- title:
--   Lemma 6.3 — gain-cost bound
-- statement:
--   Lemma 6.3 (gain-cost). Suppose there is a constant B ≥ 0 such that, for every interval j < m and every allowed entrance state s ∈ A_j, E_{Z∼U_j}[c_{j,s}(Z)] ≤ B·E_{Z∼U_j}[g_{j,s}(Z)]. Then E_{X∼U}[Cost(X)] ≤ B(1 − µ).
--
--   The allowed terminal states are live and therefore accepting. The local charge is natural-valued; its expected gain compares repaired and unrepaired blocks from the same entrance.
--
--   Differences from the source:
--   - encoding: uniform distributions and expectations on Boolean words → finite Boolean functions, PMF laws and normalized finite sums; reason: these are the same finite sample spaces and probability laws
--   - encoding: fixed transition positions and free-coordinate inputs → LiveProgram with ordered optional read positions and inputs on its free-coordinate subtype; reason: fixed layers read no input; repairs cannot change fixed choices; suffix averages over unused prefix bits cancel
--   - generalization: P in K₃,ℓ with fixed checkpoints → any partition and compatible local repair scheme; reason: the subsection explicitly makes this lemma independent of checkpoint width and collision bounds; every source scheme is included
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, Lemma 6.3, p. 31, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_LocalRepair

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

theorem lemma_6_3 {n d : ℕ} (P : LiveProgram n d) (T : CheckpointPartition d)
    (R : LocalRepair P T) (B : ℝ) (hB : 0 ≤ B)
    (localBound : ∀ (j : Fin T.intervals) (s : Fin 3), s ∈ R.allowed j.castSucc →
      average (fun z => (R.charge j s z : ℝ)) ≤ B * average (R.gain j s)) :
    average (fun x => (R.cost x : ℝ)) ≤ B * (1 - P.density)
 := by sorry

end Width4HSG.Main
