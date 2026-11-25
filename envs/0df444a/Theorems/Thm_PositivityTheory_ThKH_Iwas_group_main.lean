-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Iwas_group_main
-- name    : PositivityTheory.ThKH.Iwas.group_main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:56.113241+00:00
-- url     : https://prove2.me/theorems/81871dda-f218-4226-948f-de20ce203d6c
-- title:
--   Iwas: group main
-- statement:
--   The Iwas construction uses the group main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L101-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L101-L174

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

theorem PositivityTheory.ThKH.Iwas.group_main {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {m : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hiso : ∀ g, Iso c (Wm L (Fin m)) (Wm L (Fin m)) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (Wm L (Fin m)) (Wm L (Fin m)) M → ∃ g ∈ U, Φ g = M) (K P : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1)
    (hP : ∀ g ∈ U, (∀ i j, Φ g (Sum.inr i) (Sum.inl j) = 0) → g ∈ P) :
    (∀ h ∈ U, ∃ p ∈ P, ∃ k ∈ K, h = p * k) ∧
    ∀ χ : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, χ (k * k') = χ k * χ k') → (∀ k ∈ K, k ∈ P → χ k = 1) → ∀ k ∈ K, χ k = 1 := by sorry
