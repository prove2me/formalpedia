-- Prove2me | Theorems.Thm_P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7
-- name    : P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:37.705749+00:00
-- url     : https://prove2.me/theorems/d262d34a-0c19-448c-baf0-58385375fcf7
-- title:
--   P2 M Formalism GM M int Pol monomial  c4f29bf6f8d7: P2 M Formalism GM M int Pol monomial  c4f29bf6f8d7
-- statement:
--   The P2 M Formalism GM M int Pol monomial  c4f29bf6f8d7 construction uses the P2 M Formalism GM M int Pol monomial  c4f29bf6f8d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L505-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L505-L506

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {σ : Type}

theorem P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7 (m : σ →₀ ℕ) : (monomial m 1 : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ := by sorry

alias «Formalism».«GM».«M».«intPol_monomial'» := P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7
