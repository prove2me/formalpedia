-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_tpComap_proof__c8ee3d5f22ca
-- name    : P2M_Formalism_L2_DIV_tpComap_proof__c8ee3d5f22ca
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:33.404867+00:00
-- url     : https://prove2.me/theorems/1c910c53-76fd-4576-a994-cfb21ee4c452
-- title:
--   P2 M Formalism L2 DIV tp Comap proof  c8ee3d5f22ca: P2 M Formalism L2 DIV tp Comap proof  c8ee3d5f22ca
-- statement:
--   The P2 M Formalism L2 DIV tp Comap proof  c8ee3d5f22ca construction uses the P2 M Formalism L2 DIV tp Comap proof  c8ee3d5f22ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L897-L900
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L897-L900

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

theorem P2M_Formalism_L2_DIV_tpComap_proof__c8ee3d5f22ca (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E)
    (hc : toRInt F E c ∈ P.asIdeal.map (toRInt F E)) : c ∈ P.asIdeal := by sorry

alias «Formalism».«L2».«DIV».«tpComap_proof'» := P2M_Formalism_L2_DIV_tpComap_proof__c8ee3d5f22ca
