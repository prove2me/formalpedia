-- Prove2me | Theorems.Thm_UpperTheory_Mu_exists_monomial
-- name    : UpperTheory.Mu.exists_monomial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:04.980052+00:00
-- url     : https://prove2.me/theorems/b2f09cfd-295f-4f62-96aa-11f51a054a69
-- title:
--   Mu: exists monomial
-- statement:
--   The Mu construction uses the exists monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean#L76-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean#L76-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]

theorem UpperTheory.Mu.exists_monomial [StarRing K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : gᴴ * g = 1) (hint : ∀ a b, IsIntegral ℤ (g a b)) :
    ∃ (t : Fin n → K) (σ : Equiv.Perm (Fin n)), (∀ b, t b ^ Units.torsionOrder K = 1) ∧
      g = Matrix.of fun a b => if a = σ b then t b else 0 := by sorry
