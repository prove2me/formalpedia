-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_detE_C_mul
-- name    : PositivityTheory.Rg.Sw.SP.Mi.detE_C_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:10.7819+00:00
-- url     : https://prove2.me/theorems/f8134f0b-1eed-557d-87ee-3d2a83b7db97
-- title:
--   Mi: det E C mul
-- statement:
--   The Mi construction uses the det E C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L54-L57

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R] {ρ : ℕ}

theorem PositivityTheory.Rg.Sw.SP.Mi.detE_C_mul (α : R) (r : R) (g : Pm R ρ) : detE α (C r * g) = C r * detE α g := by sorry
