-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_hasDerivAt_of_mulHom
-- name    : PositivityTheory.Rg.Cz.hasDerivAt_of_mulHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:08.873838+00:00
-- url     : https://prove2.me/theorems/ebbe7aa1-7dfc-5d7f-aeda-e59475918e59
-- title:
--   Cz: has Deriv At of mul Hom
-- statement:
--   The Cz construction uses the has Deriv At of mul Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/ArchimedeanWhittakerDerivatives/HasDerivAtOfMulHom.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/ArchimedeanWhittakerDerivatives/HasDerivAtOfMulHom.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtOfContinuousHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WirtingerCombinationNeZero
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_ArchimedeanWhittakerDerivatives_HasDerivAtOfMulHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz

theorem PositivityTheory.Rg.Cz.hasDerivAt_of_mulHom (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) (hm : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by sorry
