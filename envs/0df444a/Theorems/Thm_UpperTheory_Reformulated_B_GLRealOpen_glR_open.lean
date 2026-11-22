-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_GLRealOpen_glR_open
-- name    : UpperTheory.Reformulated.B.GLRealOpen.glR_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:44.776781+00:00
-- url     : https://prove2.me/theorems/db640c3f-c14e-466f-a206-65dbb204a103
-- title:
--   GLReal Open: gl R open
-- statement:
--   The GLReal Open construction uses the gl R open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/GLRealOpen.lean#L4-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/GLRealOpen.lean#L4-L20

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.GLRealOpen.glR_open :
    ∀ {K : Type} [inst : CommRing K] [inst_1 : TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
      IsOpen (↑R : Set K) → ∀ (n : ℕ), IsOpen (↑(UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n) : Set (GL (Fin n) K)) := by sorry
