-- Prove2me | Theorems.Thm_P2M_Formalism_L2_PT_transp___1b8910838bef
-- name    : P2M_Formalism_L2_PT_transp___1b8910838bef
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:07.035848+00:00
-- url     : https://prove2.me/theorems/ab538f13-f655-4b62-b904-b5d079f4f627
-- title:
--   P2 M Formalism L2 PT transp   1b8910838bef: P2 M Formalism L2 PT transp   1b8910838bef
-- statement:
--   The P2 M Formalism L2 PT transp   1b8910838bef construction uses the P2 M Formalism L2 PT transp   1b8910838bef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L64-L65

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem P2M_Formalism_L2_PT_transp___1b8910838bef (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (γ : GL κ K) :
    (transp e τ).ρ γ = τ.ρ ((glEquiv K e).symm γ) := by sorry

alias «Formalism».«L2».«PT».«transp_ρ» := P2M_Formalism_L2_PT_transp___1b8910838bef
