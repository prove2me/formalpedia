-- Prove2me | Theorems.Thm_QEC_Coding_BDL26EvenC4OldXEndpoint_exists_original_even_C4_single_physical_first_zero_chi_one
-- name    : QEC.Coding.BDL26EvenC4OldXEndpoint.exists_original_even_C4_single_physical_first_zero_chi_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T14:04:45.082937+00:00
-- url     : https://prove2.me/theorems/5fa6fdf7-2cf4-4f70-acdc-9100c1421dbc
-- title:
--   BDL26 Even C4 Old XEndpoint: exists original even C4 single physical first zero chi one
-- statement:
--   At every admissible odd scale, the SAME legal original N=2 background and
--   ONE actual Physical S4 coordinate have original FIRST zero and original chiX
--   one. Their complete original deltaX is closed and is not an actual full
--   boundary. The genuine RZ cylinder root is chosen internally; callers provide
--   no geometry, coherence, H1 section or failure premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4OldXEndpoint.lean#L52-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4OldXEndpoint.lean#L52-L76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26EvenC4OldXEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open scoped Classical

theorem QEC.Coding.BDL26EvenC4OldXEndpoint.exists_original_even_C4_single_physical_first_zero_chi_one (S : OddScale) :
    ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 2,
      ∃ q : BDL26CSSHamiltonian.Physical S 4,
        BDL26ActualFailureReadout.firstReadout S 2 u=0 ∧
        BDL26LogicalDefectProtection.chiX S 2 u q=1 ∧
        BDL26CSSHamiltonian.zSyndrome S 4
          (BDL26LogicalDefectProtection.deltaX S 2 u q)=0 ∧
        BDL26LogicalDefectProtection.deltaX S 2 u q ∉ LinearMap.range
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0
            (BDL26DecodingGraph.state S 4).presentation) := by sorry
