-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f
-- name    : P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:16.559711+00:00
-- url     : https://prove2.me/theorems/e3226df8-138c-4fae-8c9c-3df6130badf3
-- title:
--   P2 M Formalism L2 DIV tp Ex U proof  f73447c0298f: P2 M Formalism L2 DIV tp Ex U proof  f73447c0298f
-- statement:
--   The P2 M Formalism L2 DIV tp Ex U proof  f73447c0298f construction uses the P2 M Formalism L2 DIV tp Ex U proof  f73447c0298f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L991-L1048
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L991-L1048

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

theorem P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) (a : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E) := by sorry

alias «Formalism».«L2».«DIV».«tpExU_proof'» := P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f
