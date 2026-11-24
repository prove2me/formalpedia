-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_N_Br___bijective_afb8fdf27d2e
-- name    : P2M_Formalism_MainNotions_N_Br___bijective_afb8fdf27d2e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:53:05.972358+00:00
-- url     : https://prove2.me/theorems/5519d2ae-c5d6-4286-aca9-903bb429dd90
-- title:
--   P2 M Formalism Main Notions N Br   bijective afb8fdf27d2e: P2 M Formalism Main Notions N Br   bijective afb8fdf27d2e
-- statement:
--   The P2 M Formalism Main Notions N Br   bijective afb8fdf27d2e construction uses the P2 M Formalism Main Notions N Br   bijective afb8fdf27d2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L743-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L743-L743

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations Module
open Formalism Formalism.MainNotions Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N.Br
variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)
variable [IsDomain O]

theorem P2M_Formalism_MainNotions_N_Br___bijective_afb8fdf27d2e : Function.Bijective (ι Bw) := by sorry

alias «Formalism».«MainNotions».«N».«Br».«ι_bijective» := P2M_Formalism_MainNotions_N_Br___bijective_afb8fdf27d2e
