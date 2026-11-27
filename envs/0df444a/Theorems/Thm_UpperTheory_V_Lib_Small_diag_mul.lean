-- Prove2me | Theorems.Thm_UpperTheory_V_Lib_Small_diag_mul
-- name    : UpperTheory.V.Lib.Small.diag_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:58.799412+00:00
-- url     : https://prove2.me/theorems/1516cd71-9520-43da-9054-00ab1b06acfc
-- title:
--   Small: diag mul
-- statement:
--   The Small construction uses the diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IntegralityNearIdentity/EqOneOfNear.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IntegralityNearIdentity/EqOneOfNear.lean#L17-L19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraAlt
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfNear
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraBis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MirabolicColumnBlock
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitelyGeneratedModPow
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_EqOneOfNear
import Theorems.Thm_UpperTheory_Reformulated_B_S8_diag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.V UpperTheory.V.Lib UpperTheory.V.Lib.Small

theorem UpperTheory.V.Lib.Small.diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a := by sorry
