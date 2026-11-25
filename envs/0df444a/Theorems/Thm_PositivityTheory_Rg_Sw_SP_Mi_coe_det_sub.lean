-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_coe_det_sub
-- name    : PositivityTheory.Rg.Sw.SP.Mi.coe_det_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:08.689191+00:00
-- url     : https://prove2.me/theorems/395a8ca1-7337-5a4e-a08f-8d06622c5e46
-- title:
--   Mi: coe det sub
-- statement:
--   The Mi construction uses the coe det sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean#L15-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_gens_comm

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

theorem PositivityTheory.Rg.Sw.SP.Mi.coe_det_sub (α : R) (ρ r : ℕ) (I J : Fin r → Fin ρ) :
    letI : CommRing (Algebra.adjoin R (gens α ρ)) := Algebra.adjoinCommRingOfComm R (gens_comm α ρ)
    ((((Aop α ρ).submatrix I J).det : Algebra.adjoin R (gens α ρ)) : Module.End R (Pm R ρ)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) •
        ((List.finRange r).map (fun k => opE α (I k) (J (σ k)))).prod := by sorry
