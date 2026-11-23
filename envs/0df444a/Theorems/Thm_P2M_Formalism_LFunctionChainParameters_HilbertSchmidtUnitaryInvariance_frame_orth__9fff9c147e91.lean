-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth__9fff9c147e91
-- name    : P2M_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth__9fff9c147e91
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:18.646131+00:00
-- url     : https://prove2.me/theorems/4cd980cc-8a7b-4e1b-ada8-425aca2f60f4
-- title:
--   P2 M Formalism LFunction Chain Parameters Hilbert Schmidt Unitary Invariance frame orth  9fff9c147e91: P2 M Formalism LFunction Chain Parameters Hilbert Schmidt Unitary Invariance frame orth  9fff9c14
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Hilbert Schmidt Unitary Invariance frame orth  9fff9c147e91 construction uses the P2 M Formalism LFunction Chain Parameters Hilbert Schmidt Unitary Invariance frame orth  9fff9c147e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L200-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsOrthonormalFrameComplement.lean#L200-L203

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {Dall D D1 : ℕ}

theorem P2M_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth__9fff9c147e91 (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : J1ᴴ * J = 0 := by sorry

alias «Formalism».«LFunctionChainParameters».«HilbertSchmidtUnitaryInvariance».«frame_orth'» := P2M_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_orth__9fff9c147e91
