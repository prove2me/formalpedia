-- Prove2me | Theorems.Thm_UpperTheory_GL_dataField
-- name    : UpperTheory.GL.dataField
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:00:47.011742+00:00
-- url     : https://prove2.me/theorems/0742a1b0-8613-5198-a020-b2a7fc42dbb9
-- title:
--   GL: data Field
-- statement:
--   The GL construction uses the data Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/dataField.lean#L33-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/dataField.lean#L33-L52

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_dataField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.dataField :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      ((∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (toE φ (H.gal σ)).toAdd ∈ (arith H.toHostRaw).inertia p) ∧
      (IsArithFrobAt ℤ σ P ↔ (toE φ (H.gal σ)).toAdd - (arith H.toHostRaw).frob p ∈ (arith H.toHostRaw).inertia p) := by sorry
