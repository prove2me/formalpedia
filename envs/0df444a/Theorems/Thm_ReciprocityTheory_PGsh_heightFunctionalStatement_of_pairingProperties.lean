-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_heightFunctionalStatement_of_pairingProperties
-- name    : ReciprocityTheory.PGsh.heightFunctionalStatement_of_pairingProperties
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:53.735794+00:00
-- url     : https://prove2.me/theorems/e6fce224-94c4-4b77-9909-01a406fb666d
-- title:
--   PGsh: height Functional Statement of pairing Properties
-- statement:
--   The PGsh construction uses the height Functional Statement of pairing Properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HeightFunctionalStatementOfPairingProperties.lean#L367-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HeightFunctionalStatementOfPairingProperties.lean#L367-L370

import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Definitions.Def_ReciprocityTheory_DualLattices_ToSigmaAddFstZeroFst
import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_HeightFunctionalStatementOfPairingProperties
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

theorem ReciprocityTheory.PGsh.heightFunctionalStatement_of_pairingProperties (B : BX R₀) (h1 : PairingPropertiesStatement B) : HighestWeightVectorUniformBounds B := by sorry
