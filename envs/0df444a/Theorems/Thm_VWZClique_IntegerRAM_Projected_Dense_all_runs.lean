-- Prove2me | Theorems.Thm_VWZClique_IntegerRAM_Projected_Dense_all_runs
-- name    : VWZClique.IntegerRAM.Projected.Dense.all_runs
-- status  : Proved
-- author  : @orz
-- created : 2026-11-20T14:07:52.717969+00:00
-- url     : https://prove2.me/theorems/e96dc4ed-1f3a-401b-a5d4-ef2013a4a1f4
-- title:
--   Computing the three clique-projection matrices on a word RAM
-- statement:
--   Given prepared memory holding the binary weights and retained projectors at a dyadic input size, the fixed word-RAM program computes the three scaled integer matrices for the projected clique trace. It uses the same square-multiplication scheme in each short slice and computes the second projection of the left matrix by the full butterfly transform. The theorem certifies every matrix entry, the asserted instruction bound, and preservation of the preceding recursion frames.
-- source:
--   V. Vassilevska Williams and O. Zamir, “The k-Clique hypothesis is dead, for good,” Theorem 1.1 and Appendix A. https://zamir.prof/kclq.pdf

import Mathlib
import Definitions.Def_VWZClique_NativeCliqueCompiler
open VWZClique VWZClique.IntegerRAM VWZClique.IntegerRAM.Structured VWZClique.IntegerRAM.Projected VWZClique.BlockMM VWZClique.Projection VWZClique.UniformFolds VWZClique.WeightedProof VWZClique.Double

theorem VWZClique.IntegerRAM.Projected.Dense.all_runs {W M L K b r c base : ℕ} (S : Scheme b r) (hb : 2≤b) (hr : 0<r)
    (π : Equiv.Perm V) (E : Finset EdgeSlot) (q : ℕ) (w : WeightKey (2^L)→ℚ)
    (hw : ∀i, Binary (literal w (inputKey π E i))) (m : Memory) (hL : 0<L) (large : 512≤base)
    (ready : Preparation.Ready L K base (Dense.labelSet K L).card b c w m)
    (room : Graph.Division.Room W M)
    (space : (Dense.Bank base L).weights+4*(2^L*2^L)+WordLayout.space b r (depth b (2^L)) 1≤M) :
    let labels := Dense.labelSet K L
    let P := S.scale^(depth b (2^L))
    let cw := fun i => literal w (inputKey π E i)
    let banks := Large.workspaceBanks (MaskScan.Arena.slot base (2^L) 7+2) (2^L)
    ∃t≤Dense.cost S π E L labels.card, ∃o, Runs W (Dense.code S π E) m t o ∧
      Preparation.Ready L K base labels.card b c w o ∧
      Large.Sources o banks (scaleMat P (shortWeight labels K cw)) (scaleMat P (middle labels q cw))
        (scaleMat P (Projected.right labels q cw)) ∧ ∀z : ℕ, projectionPrefix base (2^L) z → o z=m z := by sorry
