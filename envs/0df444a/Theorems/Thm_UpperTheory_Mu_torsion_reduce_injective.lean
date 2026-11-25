-- Prove2me | Theorems.Thm_UpperTheory_Mu_torsion_reduce_injective
-- name    : UpperTheory.Mu.torsion_reduce_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:18.526266+00:00
-- url     : https://prove2.me/theorems/69ae2150-d921-4bde-980d-78b769046430
-- title:
--   Mu: torsion reduce injective
-- statement:
--   The Mu construction uses the torsion reduce injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/TorsionReduceInjective.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/TorsionReduceInjective.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Classical
noncomputable section
open UpperTheory UpperTheory.Mu

theorem UpperTheory.Mu.torsion_reduce_injective (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
    (hw : ((NumberField.Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal) :
    Function.Injective ((Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom).comp
      (NumberField.Units.torsion L).subtype) := by sorry
