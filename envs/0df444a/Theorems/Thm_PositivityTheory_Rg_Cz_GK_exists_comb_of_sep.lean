-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_GK_exists_comb_of_sep
-- name    : PositivityTheory.Rg.Cz.GK.exists_comb_of_sep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:47:57.09158+00:00
-- url     : https://prove2.me/theorems/31f40cc4-d2ad-5333-b87b-239eaeabbdec
-- title:
--   GK: exists comb of sep
-- statement:
--   The GK construction uses the exists comb of sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/UnitaryCurves/ExistsUnitaryCurve.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/UnitaryCurves/ExistsUnitaryCurve.lean#L9-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_UnitaryCurves_ExistsUnitaryCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.GK

theorem PositivityTheory.Rg.Cz.GK.exists_comb_of_sep {V ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ev : ι → Module.Dual ℂ V) (hsep : ∀ v, (∀ i, ev i v = 0) → v = 0) (lam : Module.Dual ℂ V) :
    ∃ (s : Finset ι) (c : ι → ℂ), ∀ v, lam v = ∑ i ∈ s, c i * ev i v := by sorry
