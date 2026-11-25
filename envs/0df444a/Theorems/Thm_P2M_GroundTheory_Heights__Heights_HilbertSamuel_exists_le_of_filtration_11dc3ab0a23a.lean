-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_le_of_filtration_11dc3ab0a23a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_le_of_filtration_11dc3ab0a23a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:15.350892+00:00
-- url     : https://prove2.me/theorems/0f12921a-9c20-56e1-b507-5f934c26932e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel exists le of filtration 11dc3ab0a23a: P2 M Ground Theory Heights  Heights Hilbert Samuel exists le of filtration 11dc3ab0a23a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel exists le of filtration 11dc3ab0a23a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel exists le of filtration 11dc3ab0a23a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PModulesFromPrimes.lean#L26-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PModulesFromPrimes.lean#L26-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_le_of_filtration_11dc3ab0a23a {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (h0 : N 0 = ⊥) (htop : N (Fin.last n) = ⊤)
    (hstep : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j} ∧
      ∀ s : R, s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (p : Ideal R) [hp : p.IsPrime] (hann : Module.annihilator R M ≤ p) : ∃ j, q j ≤ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«exists_le_of_filtration» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_le_of_filtration_11dc3ab0a23a
