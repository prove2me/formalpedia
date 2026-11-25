-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Iwas_exists_reduce
-- name    : PositivityTheory.ThKH.Iwas.exists_reduce
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:05:20.261018+00:00
-- url     : https://prove2.me/theorems/0ca5cc7f-f2db-4158-a869-9486e163d511
-- title:
--   Iwas: exists reduce
-- statement:
--   The Iwas construction uses the exists reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L75-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L75-L99

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}

theorem PositivityTheory.ThKH.Iwas.exists_reduce (hc : ∀ x, c (c x) = x) (hv : ∀ x, Valued.v (c x) = Valued.v x) {m : ℕ}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hM : Iso c (Wm L (Fin m)) (Wm L (Fin m)) M) :
    ∃ k, Iso c (Wm L (Fin m)) (Wm L (Fin m)) k ∧ (∀ i j, Valued.v (k i j) ≤ 1) ∧
      ∀ i j, (k * M) (Sum.inr i) (Sum.inl j) = 0 := by sorry
