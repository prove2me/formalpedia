-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26
-- name    : P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:55.19926+00:00
-- url     : https://prove2.me/theorems/55b7066a-2cd7-4918-b82f-73f40b18c147
-- title:
--   P2 M Formalism L2 DIV map conj Transpose  e871e98cff26: P2 M Formalism L2 DIV map conj Transpose  e871e98cff26
-- statement:
--   The P2 M Formalism L2 DIV map conj Transpose  e871e98cff26 construction uses the P2 M Formalism L2 DIV map conj Transpose  e871e98cff26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L51-L57

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues

theorem P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26 {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ).map σ = (E.map σ)ᴴ := by sorry

alias «Formalism».«L2».«DIV».«map_conjTranspose'» := P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26
