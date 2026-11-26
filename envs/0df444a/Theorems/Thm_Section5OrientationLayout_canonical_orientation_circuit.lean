-- Prove2me | Theorems.Thm_Section5OrientationLayout_canonical_orientation_circuit
-- name    : Section5OrientationLayout.canonical_orientation_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:50:29.15033+00:00
-- url     : https://prove2.me/theorems/f598c496-1d3f-4367-8c8d-f0104fe0c730
-- title:
--   Canonical orientation circuit with exact basis-state readout
-- statement:
--   Let n≥1, 2^q≥2^40n² and a,f natural. On the source's canonical orientation layout there is a reversible circuit with $$|C|\le3(128(n+a+34)^4+1)+3+19(a+2)n.$$ For any array x of n (a+1)-bit estimates, any real target w and any triple s of spatial example strings, initializing the canonical split basis with the estimate bits and correctly labelled examples gives a basis output whose decoded vector is exactly oriented(w,estimateVector_f(x),s).
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CanonicalOrientation.lean, lines 9–17.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationLayout
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_orientation_postprocessor
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
namespace Section5OrientationLayout
end Section5OrientationLayout
open Section5OrientationLayout

theorem Section5OrientationLayout.canonical_orientation_circuit (n q a f : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    ∃ c : Circuit gatesRev (Section5OrientationLayout.width n q a),
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ x : Fin n → Qubits (a+1), ∀ w : EuclideanSpace ℝ (Fin n),
      ∀ s : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
        ∃ z' : Qubits (Section5OrientationLayout.width n q a),
          act c.unitary (ket ((Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s)))=
            ket z' ∧ Section5OrientationLayout.readout f z'=section5_oriented_direction w (Section5OrientationLayout.estimateVector f x) s := by sorry
