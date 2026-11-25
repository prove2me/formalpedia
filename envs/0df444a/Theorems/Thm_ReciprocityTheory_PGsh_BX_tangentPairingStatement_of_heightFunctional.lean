-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_tangentPairingStatement_of_heightFunctional
-- name    : ReciprocityTheory.PGsh.BX.tangentPairingStatement_of_heightFunctional
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:31.591362+00:00
-- url     : https://prove2.me/theorems/e3b9285a-7826-4188-b2ae-7d14208202f2
-- title:
--   BX: tangent Pairing Statement of height Functional
-- statement:
--   The BX construction uses the tangent Pairing Statement of height Functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TangentPairingStatementOfHeightFunctional.lean#L17-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TangentPairingStatementOfHeightFunctional.lean#L17-L104

import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatementOfHeightFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀)

theorem ReciprocityTheory.PGsh.BX.tangentPairingStatement_of_heightFunctional (hB2 : HighestWeightVectorUniformBounds B) : TangentPairingStatement B := by sorry
