-- Prove2me | Theorems.Thm_P2M_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mul_apply__884182e8d623
-- name    : P2M_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mul_apply__884182e8d623
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:21.396333+00:00
-- url     : https://prove2.me/theorems/ad5e0713-dd27-4661-acbb-82ad5ff90e69
-- title:
--   P2 M Formalism Quantum Determinants Bruhat Big Cell hpk mul apply  884182e8d623: P2 M Formalism Quantum Determinants Bruhat Big Cell hpk mul apply  884182e8d623
-- statement:
--   The P2 M Formalism Quantum Determinants Bruhat Big Cell hpk mul apply  884182e8d623 construction uses the P2 M Formalism Quantum Determinants Bruhat Big Cell hpk mul apply  884182e8d623 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L17-L22

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}

theorem P2M_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mul_apply__884182e8d623 (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (p j : Fin (2 * r + k + 1)) : (Hpk k r * A) p j = sgn k r p * A (sig k r p) j := by sorry

alias «Formalism».«QuantumDeterminants».«BruhatBigCell».«hpk_mul_apply'» := P2M_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mul_apply__884182e8d623
