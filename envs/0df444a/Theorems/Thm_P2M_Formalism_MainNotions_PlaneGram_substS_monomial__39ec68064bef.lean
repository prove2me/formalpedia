-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef
-- name    : P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:37.903821+00:00
-- url     : https://prove2.me/theorems/9497e124-23e1-42ee-b56a-4a7803045331
-- title:
--   P2 M Formalism Main Notions Plane Gram subst S monomial  39ec68064bef: P2 M Formalism Main Notions Plane Gram subst S monomial  39ec68064bef
-- statement:
--   The P2 M Formalism Main Notions Plane Gram subst S monomial  39ec68064bef construction uses the P2 M Formalism Main Notions Plane Gram subst S monomial  39ec68064bef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L245-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L245-L247

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)

theorem P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef (α : L × Fin r →₀ ℕ) (c : K) :
    substS ι sg S A B (monomial α c) = C (ι c) * substS ι sg S A B (monomial α 1) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«substS_monomial'» := P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef
