-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_unif
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_unif
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:18.069802+00:00
-- url     : https://prove2.me/theorems/21044762-b22a-4381-b686-32ddba46816d
-- title:
--   Multiplicative Heights: gauss unif
-- statement:
--   The Multiplicative Heights construction uses the gauss unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L51-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussValLeIffDivMem.lean#L51-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_unif {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤)
    (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (ϖ : Ω) (hdiv : ∀ y ∈ (V.comap (algebraMap Ω U)).nonunits,
      y / ϖ ∈ V.comap (algebraMap Ω U)) (z : U) (hz : z ∈ V.nonunits) :
    z / algebraMap Ω U ϖ ∈ V := by sorry
