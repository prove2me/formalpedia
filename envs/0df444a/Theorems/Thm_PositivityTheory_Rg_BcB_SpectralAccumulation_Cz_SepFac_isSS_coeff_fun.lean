-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_coeff_fun
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_coeff_fun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:07.146991+00:00
-- url     : https://prove2.me/theorems/9158c429-2b7a-5cb0-9d88-38c956dc7805
-- title:
--   Sep Fac: is SS coeff fun
-- statement:
--   The Sep Fac construction uses the is SS coeff fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean#L199-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean#L199-L311

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {A : Type} [Ring A] [Algebra ℂ A]
set_option linter.deprecated false

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_coeff_fun (m : Multiset ℂ) (hm : m.Nodup) (r s : ℕ) (_hrs : Multiset.card m = r + s) (c₁ c₂ : ℂ)
    (a b : ℕ → A) (ha : a r = 1) (hb : b s = 1)
    (hcomm : ∀ i j, Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j))
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), (u + c₁) ^ k • a k) *
      (∑ k ∈ Finset.range (s + 1), (u + c₂) ^ k • b k) = algebraMap ℂ A (m.map (u + ·)).prod) (k : ℕ) :
    (k ≤ r → IsSS (a k)) ∧ (k ≤ s → IsSS (b k)) := by sorry
