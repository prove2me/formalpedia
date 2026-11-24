-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_tpWild_proof__5005395ee64f
-- name    : P2M_Formalism_L2_DIV_tpWild_proof__5005395ee64f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:18.913996+00:00
-- url     : https://prove2.me/theorems/d0ca55d5-e5fa-4593-ae51-33d59a842ace
-- title:
--   P2 M Formalism L2 DIV tp Wild proof  5005395ee64f: P2 M Formalism L2 DIV tp Wild proof  5005395ee64f
-- statement:
--   The P2 M Formalism L2 DIV tp Wild proof  5005395ee64f construction uses the P2 M Formalism L2 DIV tp Wild proof  5005395ee64f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L921-L932
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L921-L932

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

theorem P2M_Formalism_L2_DIV_tpWild_proof__5005395ee64f (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) :
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v := by sorry

alias «Formalism».«L2».«DIV».«tpWild_proof'» := P2M_Formalism_L2_DIV_tpWild_proof__5005395ee64f
