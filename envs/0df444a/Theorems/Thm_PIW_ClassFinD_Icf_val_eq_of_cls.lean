-- Prove2me | Theorems.Thm_PIW_ClassFinD_Icf_val_eq_of_cls
-- name    : PIW.ClassFinD.Icf.val_eq_of_cls
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:08.660333+00:00
-- url     : https://prove2.me/theorems/7372bae4-70fe-4532-afc9-e6087ba509e3
-- title:
--   Icf: val eq of cls
-- statement:
--   The Icf construction uses the val eq of cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/LatticeIdealNonzero.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/LatticeIdealNonzero.lean#L26-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_LatticeIdealNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]

theorem PIW.ClassFinD.Icf.val_eq_of_cls (b b0 : (FiniteAdeleRing (𝓞 F) F)ˣ) (hb : IsIntU b) (hb0 : IsIntU b0)
    (h : cls b = cls b0) : ∃ x y : 𝓞 F, x ≠ 0 ∧ y ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) =
        v.intValuation y * Valued.v ((b0 : FiniteAdeleRing (𝓞 F) F) v) := by sorry
