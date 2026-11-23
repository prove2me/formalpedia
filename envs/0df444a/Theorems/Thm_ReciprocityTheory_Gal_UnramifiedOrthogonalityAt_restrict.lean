-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonalityAt_restrict
-- name    : ReciprocityTheory.Gal.UnramifiedOrthogonalityAt.restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:42.623464+00:00
-- url     : https://prove2.me/theorems/5de8897a-3614-4196-8539-e7ed4d13d2a5
-- title:
--   Unramified Orthogonality At: restrict
-- statement:
--   The Unramified Orthogonality At construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean#L113-L117

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem ReciprocityTheory.Gal.UnramifiedOrthogonalityAt.restrict {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : UnramifiedOrthogonalityAt A (rho.comp (Dec (F := F) A).subtype) v) :
    UnramifiedOrthogonalityResAt rho A v := by sorry
