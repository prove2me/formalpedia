-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52
-- name    : P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:25.501339+00:00
-- url     : https://prove2.me/theorems/6353b49d-a3a7-4cc2-acf1-0e71bb82bd5f
-- title:
--   P2 M Formalism Indef R Fin Four map finsum  3c600d0ebc52: P2 M Formalism Indef R Fin Four map finsum  3c600d0ebc52
-- statement:
--   The P2 M Formalism Indef R Fin Four map finsum  3c600d0ebc52 construction uses the P2 M Formalism Indef R Fin Four map finsum  3c600d0ebc52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulFinsum.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulFinsum.lean#L17-L19

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {α M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52 (φ : M →ₗ[ℂ] M') {f : α → M} (hf : (Function.support f).Finite) :
    φ (∑ᶠ i, f i) = ∑ᶠ i, φ (f i) := by sorry

alias «Formalism».«IndefR».«Fin».«Four».«map_finsum'» := P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52
