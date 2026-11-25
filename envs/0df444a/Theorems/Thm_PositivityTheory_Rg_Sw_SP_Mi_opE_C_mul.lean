-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul
-- name    : PositivityTheory.Rg.Sw.SP.Mi.opE_C_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:33.458808+00:00
-- url     : https://prove2.me/theorems/0ffbef53-eab9-4b17-a08c-17c36d1c79af
-- title:
--   Mi: op E C mul
-- statement:
--   The Mi construction uses the op E C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L30-L35

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]

theorem PositivityTheory.Rg.Sw.SP.Mi.opE_C_mul (α r : R) {ρ : ℕ} (p q : Fin ρ) (f : Pm R ρ) : opE α p q (C r * f) = C r * opE α p q f := by sorry
