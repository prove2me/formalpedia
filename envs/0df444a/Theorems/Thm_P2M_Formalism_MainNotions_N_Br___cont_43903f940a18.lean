-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_N_Br___cont_43903f940a18
-- name    : P2M_Formalism_MainNotions_N_Br___cont_43903f940a18
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:14.706491+00:00
-- url     : https://prove2.me/theorems/5d2fbc0c-6109-4902-84eb-5a8e84127956
-- title:
--   P2 M Formalism Main Notions N Br   cont 43903f940a18: P2 M Formalism Main Notions N Br   cont 43903f940a18
-- statement:
--   The P2 M Formalism Main Notions N Br   cont 43903f940a18 construction uses the P2 M Formalism Main Notions N Br   cont 43903f940a18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L684-L684
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean#L684-L684

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

theorem P2M_Formalism_MainNotions_N_Br___cont_43903f940a18 : Continuous (ι Bw) := by sorry

alias «Formalism».«MainNotions».«N».«Br».«ι_cont» := P2M_Formalism_MainNotions_N_Br___cont_43903f940a18
