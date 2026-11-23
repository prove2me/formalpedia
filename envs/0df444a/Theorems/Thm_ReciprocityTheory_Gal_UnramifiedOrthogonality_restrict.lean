-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_UnramifiedOrthogonality_restrict
-- name    : ReciprocityTheory.Gal.UnramifiedOrthogonality.restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:30.393506+00:00
-- url     : https://prove2.me/theorems/16c890f8-3483-4bf3-bd62-3ee463d20b29
-- title:
--   Unramified Orthogonality: restrict
-- statement:
--   The Unramified Orthogonality construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean#L263-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean#L263-L265

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

theorem ReciprocityTheory.Gal.UnramifiedOrthogonality.restrict (h : UnramifiedOrthogonality) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : UnramifiedOrthogonalityResAt rho A v := by sorry
