-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qf31_isCompact_box
-- name    : UpperTheory.Reformulated.B.Qf31.isCompact_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:59.816349+00:00
-- url     : https://prove2.me/theorems/ba6205f9-2d65-4652-93c4-22c0af87081f
-- title:
--   Qf31: is Compact box
-- statement:
--   The Qf31 construction uses the is Compact box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTerLast.lean#L3-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTerLast.lean#L3-L30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by sorry
