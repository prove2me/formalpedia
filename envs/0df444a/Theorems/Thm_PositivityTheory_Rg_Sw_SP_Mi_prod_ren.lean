-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_prod_ren
-- name    : PositivityTheory.Rg.Sw.SP.Mi.prod_ren
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:24.287795+00:00
-- url     : https://prove2.me/theorems/8a2a9e3e-0b72-4f66-bc4f-7703c811d3c1
-- title:
--   Mi: prod ren
-- statement:
--   The Mi construction uses the prod ren property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean#L37-L43

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
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

theorem PositivityTheory.Rg.Sw.SP.Mi.prod_ren (α : R) {r s : ℕ} (I J : Fin r ↪ Fin s) (σ : Equiv.Perm (Fin r)) (l : List (Fin r)) (f : Pm R r) :
    (l.map (fun k => opE α (I k) (J (σ k)))).prod (ren I J f) = ren I J ((l.map (fun k => opE α k (σ k))).prod f) := by sorry
