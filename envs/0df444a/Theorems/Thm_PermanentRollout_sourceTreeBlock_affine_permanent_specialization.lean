-- Prove2me | Theorems.Thm_PermanentRollout_sourceTreeBlock_affine_permanent_specialization
-- name    : PermanentRollout.sourceTreeBlock_affine_permanent_specialization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/00fb09c2-414a-4711-830a-108304e62bab
-- title:
--   PermanentRollout.sourceTreeBlock_affine_permanent_specialization
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.sourceTreeBlock_affine_permanent_specialization
    {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree (Fin (blockCount n d)))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    ∃ (sub : Fin n × Fin n → FreeAffineInput (Fin (blockVariables n d)))
      (c : ℂ), c ≠ 0 ∧
        MvPolynomial.aeval (fun ij => (sub ij).polynomial)
            (permanent n) =
          MvPolynomial.C c *
            MvPolynomial.rename
              (finProdFinEquiv :
                Fin (blockRows n d) × Fin (blockColumns n d) ≃
                  Fin (blockVariables n d))
              (sourceTreeSeparatedMinorSum
                (blockCount n d) (blockWidth d) (blockColumns n d) d tree) := by sorry
