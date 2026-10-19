-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_good_exRec_correct
-- name    : QAlgorithms.GottesmanIntro.good_exRec_correct
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T18:06:42.419293+00:00
-- url     : https://prove2.me/theorems/80a6c833-021f-443a-9ea5-8844fa14865b
-- title:
--   Good implies correct: an extended rectangle with at most t faults is correct
-- statement:
--   This is the basic correctness property of fault-tolerant gadgets: an extended rectangle that has no more faults than the code corrects behaves like the ideal location.
--
--   Fix an $[[n,1,2t+1]]$ quantum code with an ideal decoder $\mathcal D$ (a fault-free decoding circuit that corrects every error of weight at most $t$). Fix fault-tolerant gadgets for preparation of $|0\rangle$, standard-basis measurement, the gates $H$, $R_{\pi/8}$, CNOT, the wait location, and error correction (EC), satisfying the properties Meas, Prep A/B, Gate A/B and EC A/B of Definitions 2–5. Faults are Pauli errors at locations of the gadgets.
--
--   An extended rectangle (ExRec) of type $\kappa$ consists of the leading EC gadget on each input block, the gadget for $\kappa$, and the trailing EC gadget on each output block (a preparation ExRec has no leading EC, a measurement ExRec no trailing EC). It is good if its total number of faulty locations satisfies
--
--   $$
--   s_{\mathrm{lead}} + s_{\mathrm{gadget}} + s_{\mathrm{trail}} \le t .
--   $$
--
--   Then every good ExRec is correct:
--
--   1. Gate or wait ExRec with logical gate $U$ on $k$ blocks: $\mathcal D^{\otimes k}\circ \mathrm{EC}^{\mathrm{trail}}\circ G_U\circ \mathrm{EC}^{\mathrm{lead}} = \mathcal U\circ \mathcal D^{\otimes k}\circ \mathrm{EC}^{\mathrm{lead}}$, where $\mathcal U(\rho)=U\rho U^\dagger$ (diagram (72)).
--   2. Preparation ExRec: $\mathcal D(\mathrm{EC}^{\mathrm{trail}}(\rho_{\mathrm{prep}})) = |0\rangle\langle 0|$ (diagram (73)).
--   3. Measurement ExRec: for each outcome $\beta$, the probability weight of decoded outcome $\beta$ of the measurement gadget after the leading EC equals $\langle\beta|\mathcal D(\mathrm{EC}^{\mathrm{lead}}(\rho))|\beta\rangle$ (diagram (74)).
--
--   All equalities are equalities of superoperators, so they hold on every input, including parts of entangled states; the faults on both sides are the same.
--
--   Theorem 6 is the step from gadget-level fault tolerance to circuit-level simulation (Theorem 7) and level reduction.
--
--   **Formalization Note** The protocol is `FTProtocol` with the hypothesis `IsFaultTolerant` (Defs. 2–5, the code is an $[[n,1,2t+1]]$ code, the decoder is ideal). The gadgets are concrete circuits of locations; their superoperators under a Pauli fault arrangement are computed from the circuit semantics. A full ExRec is the truncation set $\emptyset$.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 35, §5.1, Theorem 6. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

/-- Gottesman intro p.35, Theorem 6 (Good implies correct): "A good ExRec is correct."
Let `P` be a fault-tolerant protocol for an `[[n, 1, 2t + 1]]` code (gadgets satisfying
Defs. 2–5 with the ideal decoder of Def. 1). For every location type `κ` (preparation,
measurement, `H`, `R_{π/8}`, CNOT, wait) and every Pauli fault arrangement `F` of a full ExRec
of type `κ` (leading ECs, the gadget, trailing ECs; Def. 7) with at most `t` faults in total
(good, Def. 9), the ExRec is correct (Def. 8, diagrams (72)–(74)). -/
theorem good_exRec_correct (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (F : ExRecFaults κ) (hgood : F.count P ∅ ≤ P.t) :
    ExRecCorrect P κ F ∅ := by
  sorry




end QAlgorithms.GottesmanIntro
