-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_map_pbE_symm
-- name    : ReciprocityTheory.PGsh.Up.map_pbE_symm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:46.321636+00:00
-- url     : https://prove2.me/theorems/cc573dc1-d44e-4034-892b-0e77a113d582
-- title:
--   Up: map pb E symm
-- statement:
--   The Up construction uses the map pb E symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L41-L49

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

theorem ReciprocityTheory.PGsh.Up.map_pbE_symm (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))).map (pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)) = M := by sorry
