-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedDecoderGibbs_actual_energy_projector
-- name    : QEC.Coding.BDL26PairedDecoderGibbs.actual_energy_projector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:17:35.090885+00:00
-- url     : https://prove2.me/theorems/0522f8d7-c778-4835-94ea-188dbd09c6ee
-- title:
--   BDL26 Paired Decoder Gibbs: actual energy projector
-- statement:
--   The canonical same-H spectral projector, for every real energy including absent ones.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L231-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/PairedDecoderGibbs.lean#L231-L238

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24

theorem QEC.Coding.BDL26PairedDecoderGibbs.actual_energy_projector (E : ℝ) :
    Davies.hamiltonianEnergyProjector (hamiltonian S (n+2))
        (CSSGibbs.hamiltonian_symmetric _ _) E = groupedEnergyProjector S n E := by sorry
