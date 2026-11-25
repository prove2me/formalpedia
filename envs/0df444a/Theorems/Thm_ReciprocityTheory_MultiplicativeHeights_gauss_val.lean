-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_val
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:21.025169+00:00
-- url     : https://prove2.me/theorems/cc419e8c-5634-4806-9278-9cbec8dedefa
-- title:
--   Multiplicative Heights: gauss val
-- statement:
--   The Multiplicative Heights construction uses the gauss val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValExists.lean#L168-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValExists.lean#L168-L183

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_val {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) :
    V.valuation (aeval t p) = p.support.sup fun α => V.valuation (algebraMap Ω U (p.coeff α)) := by sorry
