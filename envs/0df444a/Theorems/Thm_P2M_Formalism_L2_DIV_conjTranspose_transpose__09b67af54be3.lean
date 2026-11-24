-- Prove2me | Theorems.Thm_P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3
-- name    : P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:43.894104+00:00
-- url     : https://prove2.me/theorems/27932f36-9483-48c5-b310-e3f2a209a37d
-- title:
--   P2 M Formalism L2 DIV conj Transpose transpose  09b67af54be3: P2 M Formalism L2 DIV conj Transpose transpose  09b67af54be3
-- statement:
--   The P2 M Formalism L2 DIV conj Transpose transpose  09b67af54be3 construction uses the P2 M Formalism L2 DIV conj Transpose transpose  09b67af54be3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L289-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L289-L292

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions

theorem P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3 {K : Type} [Field K] [StarRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (Aᵀ)ᴴ = (Aᴴ)ᵀ := by sorry

alias «Formalism».«L2».«DIV».«conjTranspose_transpose'» := P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3
