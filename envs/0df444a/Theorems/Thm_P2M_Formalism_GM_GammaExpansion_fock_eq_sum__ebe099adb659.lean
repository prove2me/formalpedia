-- Prove2me | Theorems.Thm_P2M_Formalism_GM_GammaExpansion_fock_eq_sum__ebe099adb659
-- name    : P2M_Formalism_GM_GammaExpansion_fock_eq_sum__ebe099adb659
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:13.397746+00:00
-- url     : https://prove2.me/theorems/ffe7b427-a62f-4252-806c-b5169b98b865
-- title:
--   P2 M Formalism GM Gamma Expansion fock eq sum  ebe099adb659: P2 M Formalism GM Gamma Expansion fock eq sum  ebe099adb659
-- statement:
--   The P2 M Formalism GM Gamma Expansion fock eq sum  ebe099adb659 construction uses the P2 M Formalism GM Gamma Expansion fock eq sum  ebe099adb659 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L125-L128

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem P2M_Formalism_GM_GammaExpansion_fock_eq_sum__ebe099adb659 (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : G.support ⊆ s) :
    M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * fw p m := by sorry

alias «Formalism».«GM».«GammaExpansion».«fock_eq_sum'» := P2M_Formalism_GM_GammaExpansion_fock_eq_sum__ebe099adb659
