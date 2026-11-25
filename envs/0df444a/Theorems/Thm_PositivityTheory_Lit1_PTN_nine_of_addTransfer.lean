-- Prove2me | Theorems.Thm_PositivityTheory_Lit1_PTN_nine_of_addTransfer
-- name    : PositivityTheory.Lit1.PTN.nine_of_addTransfer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:27.781727+00:00
-- url     : https://prove2.me/theorems/b09df897-38f0-44c6-846e-774202fd81bf
-- title:
--   PTN: nine of add Transfer
-- statement:
--   The PTN construction uses the nine of add Transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsAddTransfer.lean#L35-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsAddTransfer.lean#L35-L91

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsAddTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN

theorem PositivityTheory.Lit1.PTN.nine_of_addTransfer {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    {B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : Type} [AddCommGroup B0] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4] [AddCommGroup B5] [AddCommGroup B6] [AddCommGroup B7] [AddCommGroup BetaSesquilinearity]
    (f0 : A0 →ₗ[ZMod N] A1) (f1 : A1 →ₗ[ZMod N] A2) (f3 : A3 →ₗ[ZMod N] A4)
    (f4 : A4 →ₗ[ZMod N] A5) (f6 : A6 →ₗ[ZMod N] A7) (f7 : A7 →ₗ[ZMod N] A8)
    (g0 : B0 →+ B1) (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (g5 : B5 →+ B6) (g6 : B6 →+ B7) (g7 : B7 →+ BetaSesquilinearity)
    (e0 : A0 ≃+ B0) (e1 : A1 ≃+ B1) (e2 : A2 ≃+ B2) (e3 : A3 ≃+ B3) (e4 : A4 ≃+ B4)
    (e5 : A5 ≃+ B5) (e6 : A6 ≃+ B6) (e7 : A7 ≃+ B7) (e8 : A8 ≃+ BetaSesquilinearity) (ε : Fin 6 → ℤˣ)
    (h0 : ∀ a, g0 (e0 a) = (ε 0 : ℤ) • e1 (f0 a)) (h1 : ∀ a, g1 (e1 a) = (ε 1 : ℤ) • e2 (f1 a))
    (h3 : ∀ a, g3 (e3 a) = (ε 2 : ℤ) • e4 (f3 a)) (h4 : ∀ a, g4 (e4 a) = (ε 3 : ℤ) • e5 (f4 a))
    (h6 : ∀ a, g6 (e6 a) = (ε 4 : ℤ) • e7 (f6 a)) (h7 : ∀ a, g7 (e7 a) = (ε 5 : ℤ) • e8 (f7 a))
    (hx : Function.Injective g0 ∧ Function.Exact g0 g1 ∧ Function.Exact g1 g2 ∧
      Function.Exact g2 g3 ∧ Function.Exact g3 g4 ∧ Function.Exact g4 g5 ∧ Function.Exact g5 g6 ∧
      Function.Exact g6 g7 ∧ Function.Surjective g7) :
    ∃ (δ₁ : A2 →ₗ[ZMod N] A3) (δ₂ : A5 →ₗ[ZMod N] A6),
      Function.Injective f0 ∧ Function.Exact f0 f1 ∧ Function.Exact f1 δ₁ ∧ Function.Exact δ₁ f3 ∧
      Function.Exact f3 f4 ∧ Function.Exact f4 δ₂ ∧ Function.Exact δ₂ f6 ∧ Function.Exact f6 f7 ∧
      Function.Surjective f7 := by sorry
