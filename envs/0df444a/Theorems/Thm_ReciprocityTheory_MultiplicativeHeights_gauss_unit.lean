-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_unit
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_unit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:04.963913+00:00
-- url     : https://prove2.me/theorems/cd5879a0-9b4a-5fa8-922b-449bf89d5287
-- title:
--   Multiplicative Heights: gauss unit
-- statement:
--   The Multiplicative Heights construction uses the gauss unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValExists.lean#L86-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValExists.lean#L86-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.gauss_unit {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U))
    (α₀ : σ →₀ ℕ) (hα₀ : (p.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U)) (h0 : p.coeff α₀ ≠ 0) :
    V.valuation (aeval t p) = 1 := by sorry
