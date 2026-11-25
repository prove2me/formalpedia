-- Prove2me | Theorems.Thm_UpperTheory_V_length_eq_add_eigen
-- name    : UpperTheory.V.length_eq_add_eigen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:54.636875+00:00
-- url     : https://prove2.me/theorems/c187f46b-bfcc-4feb-a7ca-4c6bfd2ab13a
-- title:
--   V: length eq add eigen
-- statement:
--   The V construction uses the length eq add eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean#L10-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean#L10-L55

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.Top
open UpperTheory UpperTheory.V

theorem UpperTheory.V.length_eq_add_eigen {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (h2 : IsUnit (2 : R))
    (N : Submodule R M) (f : Module.End R M) (hN : ∀ x ∈ N, f x ∈ N) (hf : ∀ x, f (f x) = x) (s : R) (hs : s * s = 1) :
    Module.length R N = Module.length R ↥(N ⊓ f.eigenspace s) + Module.length R ↥(N ⊓ f.eigenspace (-s)) := by sorry
