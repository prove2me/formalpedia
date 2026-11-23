-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_LocalEulerCharAt_restrict
-- name    : ReciprocityTheory.Gal.LocalEulerCharAt.restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:43.734812+00:00
-- url     : https://prove2.me/theorems/a1e4f43c-6104-4fda-bf9a-9cc2c4917811
-- title:
--   Local Euler Char At: restrict
-- statement:
--   The Local Euler Char At construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean#L119-L122

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

theorem ReciprocityTheory.Gal.LocalEulerCharAt.restrict {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : LocalEulerCharAt A (rho.comp (Dec (F := F) A).subtype) v) : LocalEulerCharResAt rho A v := by sorry
