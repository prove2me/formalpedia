-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_output_eq_of_all_good
-- name    : QAlgorithms.GottesmanIntro.output_eq_of_all_good
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:06:20.184104+00:00
-- url     : https://prove2.me/theorems/4524ee0b-90d3-4e42-9f11-d9fd5c5fee47
-- title:
--   A fault-tolerant circuit with only good ExRecs has the ideal output distribution
-- statement:
--   This theorem says that a fault-tolerant simulation is exact as long as no extended rectangle has too many faults.
--
--   Let $C$ be a quantum circuit of preparation, gate ($H$, $R_{\pi/8}$, CNOT), measurement and wait locations, organized in time steps as in Definition 6: it takes no input, every qubit is first prepared and finally measured, and at each time step every live qubit is in exactly one location. Fix an $[[n,1,2t+1]]$ code with ideal decoder and fault-tolerant gadgets satisfying Definitions 2–5, all location gadgets having the same depth. Let $C'$ be the fault-tolerant circuit for $C$: each location replaced by its gadget, with EC gadgets inserted between consecutive locations.
--
--   Let a Pauli fault arrangement be given on $C'$ such that every extended rectangle of $C'$ contains at most $t$ faulty locations. Write $p_{C'}$ for the distribution of the measurement record of the faulty $C'$, decoded classically to one bit per measurement location of $C$ by the measurement gadgets' classical decoding, and $p_C$ for the output distribution of the ideal circuit $C$. Then
--
--   $$
--   p_{C'} = p_C .
--   $$
--
--   This is the first form of the statement that fault tolerance protects a computation; Theorem 8 extends it to circuits with bad extended rectangles.
--
--   **Formalization Note** The fault-tolerant circuit is `ftCircuit P C`; its measurement record is pushed forward along `ftDecode P C`. The common gadget depth (`HasUniformDepth`) is the layer's modelling hypothesis that lets the gadgets of one time step of $C$ run in parallel without extra unprotected waiting locations.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 36, §5.2, Theorem 7. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro


/-- Gottesman intro p.36, Theorem 7: "Suppose a fault-tolerant circuit for `C` contains only
good extended rectangles. Then the output distribution of the fault-tolerant protocol is the same
as the output distribution of `C`." Let `P` be a fault-tolerant protocol (Defs. 2–5) whose
location gadgets have a common depth, and `C` a circuit of preparation, gate, measurement and
wait locations as in Def. 6 (no input, every qubit prepared first and measured last). Let `fa`
be a Pauli fault arrangement on the fault-tolerant circuit `C′ = ftCircuit P C` such that every
(full) ExRec of `C′` contains at most `t` faulty locations. Then the distribution of the
measurement record of the faulty `C′`, decoded classically by the measurement gadgets'
decoding (`ftDecode`), equals the output distribution of the ideal circuit `C`. -/
theorem output_eq_of_all_good (P : FTProtocol) (hP : P.IsFaultTolerant)
    (hdepth : P.HasUniformDepth) {N : ℕ} (C : LocCircuit N) (hC : C.IsIdealCircuit)
    (fa : PauliArrangement)
    (hgood : ∀ ℓ ∈ C.locs, (faultyLocs (ftCircuit P C) fa ∩ exRecLocs P C ℓ ∅).card ≤ P.t) :
    pushDist (ftDecode P C) ((ftCircuit P C).outDist (pauliErr (ftCircuit P C) fa) 1) =
      C.idealOutDist := by
  sorry



end QAlgorithms.GottesmanIntro
