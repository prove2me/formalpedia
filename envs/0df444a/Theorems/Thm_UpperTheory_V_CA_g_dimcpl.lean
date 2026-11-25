-- Prove2me | Theorems.Thm_UpperTheory_V_CA_g_dimcpl
-- name    : UpperTheory.V.CA.g_dimcpl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:57.443494+00:00
-- url     : https://prove2.me/theorems/d5d818c7-4f6d-4232-8a2e-d698bc024102
-- title:
--   CA: g dimcpl
-- statement:
--   The CA construction uses the g dimcpl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/GDimcpl.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebraHeight/GDimcpl.lean#L6-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_GDimcpl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing

theorem UpperTheory.V.CA.g_dimcpl :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by sorry
