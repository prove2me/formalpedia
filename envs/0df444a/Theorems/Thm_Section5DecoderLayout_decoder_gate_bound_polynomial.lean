-- Prove2me | Theorems.Thm_Section5DecoderLayout_decoder_gate_bound_polynomial
-- name    : Section5DecoderLayout.decoder_gate_bound_polynomial
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:38.711532+00:00
-- url     : https://prove2.me/theorems/4533c858-f5ec-5af5-ad66-add38b537465
-- title:
--   Polynomial envelope for the canonical decoder gate bound
-- statement:
--   Let N,b,f be natural numbers and P a real number satisfying P≥1, N+1≤P, b+1≤P and f+2≤P. Let G(N,b,f) be the canonical decoder gate-count expression defined in the source, combining column-score arithmetic, maximum-record selection, real/imaginary selection and fixed-point output. Then
--
--   $$G(N,b,f)≤500P^5.$$
-- source:
--   Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Original auxiliary complexity bound. Exact formalization: Solutions/Section5DecoderGateBound.lean, lines 8–10; the gate-count expression is defined in Solutions/Section5IntegerDirectionCircuit.lean, lines 10–14.

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
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Mathlib
set_option autoImplicit false
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.decoder_gate_bound_polynomial (N b f : ℕ) (P : ℝ) (hP : 1 ≤ P)
    (hn : ((N+1:ℕ):ℝ) ≤ P) (hb : ((b+1:ℕ):ℝ) ≤ P) (hf : ((f+2:ℕ):ℝ) ≤ P) :
    (Section5DecoderLayout.decoderGateBound N b f:ℝ) ≤ 500*P^5 := by sorry
