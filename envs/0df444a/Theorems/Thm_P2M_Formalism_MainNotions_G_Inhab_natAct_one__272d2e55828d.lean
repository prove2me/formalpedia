-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_G_Inhab_natAct_one__272d2e55828d
-- name    : P2M_Formalism_MainNotions_G_Inhab_natAct_one__272d2e55828d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:00.531468+00:00
-- url     : https://prove2.me/theorems/fba64759-6d04-485e-a08c-ff2daec087fc
-- title:
--   P2 M Formalism Main Notions G Inhab nat Act one  272d2e55828d: P2 M Formalism Main Notions G Inhab nat Act one  272d2e55828d
-- statement:
--   The P2 M Formalism Main Notions G Inhab nat Act one  272d2e55828d construction uses the P2 M Formalism Main Notions G Inhab nat Act one  272d2e55828d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L144-L145

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (C : Level P)
variable (h0 : ∀ v, P.lam0 v = fun _ _ => 0)
include h0

theorem P2M_Formalism_MainNotions_G_Inhab_natAct_one__272d2e55828d (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) : P.natAct A 1 = 1 := by sorry

alias «Formalism».«MainNotions».«G».«Inhab».«natAct_one'» := P2M_Formalism_MainNotions_G_Inhab_natAct_one__272d2e55828d
