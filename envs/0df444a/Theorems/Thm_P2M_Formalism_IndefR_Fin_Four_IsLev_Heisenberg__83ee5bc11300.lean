-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_IsLev_Heisenberg__83ee5bc11300
-- name    : P2M_Formalism_IndefR_Fin_Four_IsLev_Heisenberg__83ee5bc11300
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:32.152898+00:00
-- url     : https://prove2.me/theorems/df67629a-c608-54c4-8402-76f13a313cf0
-- title:
--   P2 M Formalism Indef R Fin Four Is Lev Heisenberg  83ee5bc11300: P2 M Formalism Indef R Fin Four Is Lev Heisenberg  83ee5bc11300
-- statement:
--   The P2 M Formalism Indef R Fin Four Is Lev Heisenberg  83ee5bc11300 construction uses the P2 M Formalism Indef R Fin Four Is Lev Heisenberg  83ee5bc11300 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L217-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L217-L256

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hY hXY hχl hχr hχ0 hLL

theorem P2M_Formalism_IndefR_Fin_Four_IsLev_Heisenberg__83ee5bc11300 {k m : ℕ} {G : V} (hG : IsLev ρ L X Y k G) {u : W} (hu : u ∈ Y) (hmu : m • u ∈ L) :
    IsLev ρ L X Y (k * m) (ρ u G) := by sorry

alias «Formalism».«IndefR».«Fin».«Four».«IsLev».«Heisenberg₂» := P2M_Formalism_IndefR_Fin_Four_IsLev_Heisenberg__83ee5bc11300
