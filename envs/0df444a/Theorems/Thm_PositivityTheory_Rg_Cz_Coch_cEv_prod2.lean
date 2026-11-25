-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_Coch_cEv_prod2
-- name    : PositivityTheory.Rg.Cz.Coch.cEv_prod2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:09.698823+00:00
-- url     : https://prove2.me/theorems/f77fd933-cdd4-450b-bb29-39447e39cda2
-- title:
--   Coch: c Ev prod2
-- statement:
--   The Coch construction uses the c Ev prod2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean#L34-L51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]

theorem PositivityTheory.Rg.Cz.Coch.cEv_prod2 {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → Fin N → H → ℂ) (c : ι → κ → V)
    (A B : Fin N → H) :
    cEv (fun v => ∑ x, ∑ y, (∏ k, f x y k (v k)) • c x y) A B =
      ∑ x, ∑ y, (∏ k, (f x y k (A k) - I * f x y k (B k))) • c x y := by sorry
