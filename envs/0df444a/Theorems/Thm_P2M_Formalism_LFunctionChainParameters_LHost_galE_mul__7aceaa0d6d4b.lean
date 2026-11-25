-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_LHost_galE_mul__7aceaa0d6d4b
-- name    : P2M_Formalism_LFunctionChainParameters_LHost_galE_mul__7aceaa0d6d4b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:23.022778+00:00
-- url     : https://prove2.me/theorems/aaf91695-88ea-4018-9faf-41a65aec684b
-- title:
--   P2 M Formalism LFunction Chain Parameters LHost gal E mul  7aceaa0d6d4b: P2 M Formalism LFunction Chain Parameters LHost gal E mul  7aceaa0d6d4b
-- statement:
--   The P2 M Formalism LFunction Chain Parameters LHost gal E mul  7aceaa0d6d4b construction uses the P2 M Formalism LFunction Chain Parameters LHost gal E mul  7aceaa0d6d4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L777-L779
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean#L777-L779

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostInertia
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_frob
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
open NumberField Ideal
open Formalism.FrobeniusOrbits (hostE galE aE bE hostGalois hostGalSpec hostInertia hostDecomp hostFrob_of)
open Formalism.TwoAdicCyclotomicDecomposition (IsLayer galMap layerGalois odd_cyc_frob odd_frob_sgn odd_card_under odd_intCast_mem_iff)
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem P2M_Formalism_LFunctionChainParameters_LHost_galE_mul__7aceaa0d6d4b (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ := by sorry

alias «Formalism».«LFunctionChainParameters».«LHost».«galE_mul'» := P2M_Formalism_LFunctionChainParameters_LHost_galE_mul__7aceaa0d6d4b
