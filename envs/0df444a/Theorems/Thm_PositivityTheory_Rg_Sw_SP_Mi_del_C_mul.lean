-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_del_C_mul
-- name    : PositivityTheory.Rg.Sw.SP.Mi.del_C_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:52.47198+00:00
-- url     : https://prove2.me/theorems/c1e0d248-e117-477c-bc25-61996612d2c9
-- title:
--   Mi: del C mul
-- statement:
--   The Mi construction uses the del C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L11-L12

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

theorem PositivityTheory.Rg.Sw.SP.Mi.del_C_mul (p q : Fin ρ) (r : R) (g : Pm R ρ) : del p q (C r * g) = C r * del p q g := by sorry
