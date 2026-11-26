-- Prove2me | Theorems.Thm_Section5OrientationLayout_canonical_mixed_orientation_success
-- name    : Section5OrientationLayout.canonical_mixed_orientation_success
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T21:12:12.105544+00:00
-- url     : https://prove2.me/theorems/f80268a0-853b-4c2c-809f-9c25ef817b96
-- title:
--   Conditional orientation success for a mixed estimate register
-- statement:
--   Let n≥1, 2^q≥2^40n² and a,f natural. There exists a reversible canonical orientation circuit with $$|C|\le3(128(n+a+34)^4+1)+3+19(a+2)n.$$ Let σ be any matrix on the data basis with nonnegative real diagonal, w real unit and 0<ε<1. Suppose diagonal mass at least 11/12 belongs to clean, nonzero fixed-point estimates whose normalized direction is within ε/6 of ±w, as specified by GoodEstimate in the source. On σ tensored with three QEX states, its decoded output v has measurement functional Pr[v≠0 and ‖v/‖v‖−w‖≤ε]≥73/96. The estimate-mass hypothesis is assumed.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MixedOrientationSuccess.lean, lines 17–26. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5MixedOrientationSuccess
import Definitions.Def_Section5Verified_Section5MixedQEXMeasurement
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationLayout
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_Section5OrientationLayout_canonical_orientation_circuit
import Theorems.Thm_section5_finite_conditioned_success
import Theorems.Thm_section5_mixed_three_qex_probability
import Theorems.Thm_section5_raw_orientation_success
import Theorems.Thm_section5_reversible_circuit_permutation
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement QuantumLTF.Example
namespace Section5OrientationLayout
end Section5OrientationLayout
open Section5OrientationLayout

open Classical in
theorem Section5OrientationLayout.canonical_mixed_orientation_success (n q a f : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    ∃ c : Circuit gatesRev (Section5OrientationLayout.width n q a),
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ σ : Matrix (Section5OrientationLayout.DataWire n a → Bool) (Section5OrientationLayout.DataWire n a → Bool) ℂ,
        (∀ d, 0 ≤ (σ d d).re) → ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∑ d, if Section5OrientationLayout.GoodEstimate f ε w d then (σ d d).re else 0) ≥ 11/12 →
        probMixed c.unitary (section5_mixed_qex_density (Section5OrientationLayout.split n q a) σ w)
          (fun z => Section5OrientationLayout.readout f z ≠ 0 ∧ ‖NormedSpace.normalize (Section5OrientationLayout.readout f z)-w‖ ≤ ε) ≥ 73/96 := by sorry
