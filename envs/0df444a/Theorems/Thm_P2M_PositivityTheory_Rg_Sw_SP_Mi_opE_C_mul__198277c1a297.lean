-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul__198277c1a297
-- name    : P2M_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul__198277c1a297
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:40.748339+00:00
-- url     : https://prove2.me/theorems/99ae43a3-be98-42d4-92fe-4ce2b5153690
-- title:
--   P2 M Positivity Theory Rg Sw SP Mi op E C mul  198277c1a297: P2 M Positivity Theory Rg Sw SP Mi op E C mul  198277c1a297
-- statement:
--   The P2 M Positivity Theory Rg Sw SP Mi op E C mul  198277c1a297 construction uses the P2 M Positivity Theory Rg Sw SP Mi op E C mul  198277c1a297 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L14-L16

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

theorem P2M_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul__198277c1a297 (α : R) (p q : Fin ρ) (r : R) (g : Pm R ρ) : opE α p q (C r * g) = C r * opE α p q g := by sorry

alias «PositivityTheory».«Rg».«Sw».«SP».«Mi».«opE_C_mul'» := P2M_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul__198277c1a297
