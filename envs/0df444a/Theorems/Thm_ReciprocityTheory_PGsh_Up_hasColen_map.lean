-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_hasColen_map
-- name    : ReciprocityTheory.PGsh.Up.hasColen_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:39.029064+00:00
-- url     : https://prove2.me/theorems/094ae1f6-c9c1-4756-978b-16c763dbc0f1
-- title:
--   Up: has Colen map
-- statement:
--   The Up construction uses the has Colen map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L36-L39

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

theorem ReciprocityTheory.PGsh.Up.hasColen_map (v : Valuation C NNReal) (e : X ≃+ Y) (M : Submodule R (Y → C)) (c : NNReal)
    (h : HasColen R v M c) : HasColen R v (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) c := by sorry
