-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_tpOff_proof__b4afce82c913
-- name    : P2M_Formalism_L2_DIV_tpOff_proof__b4afce82c913
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:23:38.195887+00:00
-- url     : https://prove2.me/theorems/f70e8484-3b87-454d-ba49-2278cb62b2ce
-- title:
--   P2 M Formalism L2 DIV tp Off proof  b4afce82c913: P2 M Formalism L2 DIV tp Off proof  b4afce82c913
-- statement:
--   The P2 M Formalism L2 DIV tp Off proof  b4afce82c913 construction uses the P2 M Formalism L2 DIV tp Off proof  b4afce82c913 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L807-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L807-L812

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem P2M_Formalism_L2_DIV_tpOff_proof__b4afce82c913 (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : P.asIdeal.under (𝓞 F) ≠ v.asIdeal) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v) :
    (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E) := by sorry

alias «Formalism».«L2».«DIV».«tpOff_proof'» := P2M_Formalism_L2_DIV_tpOff_proof__b4afce82c913
