-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_pi
-- name    : ReciprocityTheory.PGsh.Up.hasLen_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:06.849029+00:00
-- url     : https://prove2.me/theorems/129a1d85-9982-4864-a191-3c1b66254926
-- title:
--   Up: has Len pi
-- statement:
--   The Up construction uses the has Len pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L30-L33

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.hasLen_pi {C : Type} [Field C] (v : Valuation C NNReal) [Algebra R C] {d : ℕ} (a : Fin d → R) :
    HasLen v R ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {a j} : Submodule R R)))
      (∏ j, v (algebraMap R C (a j))) := by sorry
