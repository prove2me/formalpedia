-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_source_even_gibbs
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.source_even_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:23:51.296757+00:00
-- url     : https://prove2.me/theorems/2dbf7a2b-d0bd-45ac-bde7-66455a627b98
-- title:
--   BDL26 Paired Decoder Gibbs: source even gibbs
-- statement:
--   Every source-even physical level is covered, including C2 at k=1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L578-L583
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L578-L583

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_416

theorem QEC.Coding.BDL26PairedDecoderGibbs.source_even_gibbs (k : Nat) (hk : 1 ≤ k) (beta : ℝ) :
    ∃ n : Nat, n+2 = 2*k ∧
      channel S n (gibbs S (n+2) beta).toOperator = (2 : ℂ)⁻¹ • groundProjector S n ∧
      readout S n (gibbs S (n+2) beta).toOperator = ThermalEncoding.PauliLikePair.maximallyMixedQubit.toOperator := by sorry
