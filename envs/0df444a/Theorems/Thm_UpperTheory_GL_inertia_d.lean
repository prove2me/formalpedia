-- Prove2me | Theorems.Thm_UpperTheory_GL_inertia_d
-- name    : UpperTheory.GL.inertia_d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:28.105211+00:00
-- url     : https://prove2.me/theorems/17f953f9-345a-4e87-9da0-041546338494
-- title:
--   GL: inertia d
-- statement:
--   The GL construction uses the inertia d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/InertiaD.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/InertiaD.lean#L7-L49

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_InertiaD
import Theorems.Thm_P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.inertia_d :
    ∀ {φ : Frame} (H : HostAx φ), (∀ x, x ∈ (arith H.toHostRaw).inertia H.d ↔ x = 0 ∨ x = sgc0) ∧
      ((arith H.toHostRaw).frob H.d).1.2 = 1 ∧
      ∀ i : ℕ, ∃! g : E0 × φ.A, g - i • (arith H.toHostRaw).frob H.d ∈ (arith H.toHostRaw).inertia H.d ∧ ¬ InPhi g := by sorry
