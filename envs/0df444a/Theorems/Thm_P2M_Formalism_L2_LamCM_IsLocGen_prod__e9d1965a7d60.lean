-- Prove2me | Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60
-- name    : P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:15.550725+00:00
-- url     : https://prove2.me/theorems/de3c29aa-4c39-41e3-a274-051ae78eaf3b
-- title:
--   P2 M Formalism L2 Lam CM Is Loc Gen prod  e9d1965a7d60: P2 M Formalism L2 Lam CM Is Loc Gen prod  e9d1965a7d60
-- statement:
--   The P2 M Formalism L2 Lam CM Is Loc Gen prod  e9d1965a7d60 construction uses the P2 M Formalism L2 Lam CM Is Loc Gen prod  e9d1965a7d60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L401-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L401-L410

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}

theorem P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60 {ι : Type} (s : Finset ι) (a : ι → K) (I : ι → FractionalIdeal (𝓞 K)⁰ K)
    (h : ∀ i, IsLocGen p (a i) (I i)) (hI : ∀ i, I i ≠ 0) : IsLocGen p (∏ i ∈ s, a i) (∏ i ∈ s, I i) := by sorry

alias «Formalism».«L2».«LamCM».«IsLocGen».«prod'» := P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60
