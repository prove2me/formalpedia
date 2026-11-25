-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_sqIdeal_le
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.sqIdeal_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:08.196088+00:00
-- url     : https://prove2.me/theorems/315946a1-5dc7-4ded-970c-9696bcbb4ead
-- title:
--   Pullback Hopf Order: sq Ideal le
-- statement:
--   The Pullback Hopf Order construction uses the sq Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemAugIdeal.lean#L17-L24

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.sqIdeal_le {X Y : Type} (F : (X → C) →ₗ[R] (Y → C))
    (hF : ∀ f g, F (f * g) = F f * F g) {I : Submodule R (X → C)} {J : Submodule R (Y → C)}
    (hIJ : ∀ f ∈ I, F f ∈ J) : sqIdeal I ≤ (sqIdeal J).comap F := by sorry
