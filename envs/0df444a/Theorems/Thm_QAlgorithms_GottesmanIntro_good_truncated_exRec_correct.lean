-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_good_truncated_exRec_correct
-- name    : QAlgorithms.GottesmanIntro.good_truncated_exRec_correct
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:06:03.998492+00:00
-- url     : https://prove2.me/theorems/b37f29ba-5f2e-4054-b9c5-b0426d539214
-- title:
--   A good truncated ExRec is correct for ideal decoders and *-decoders
-- statement:
--   This lemma extends Theorem 6 to the truncated extended rectangles that appear when bad rectangles are pushed through in level reduction.
--
--   Fix an $[[n,1,2t+1]]$ code with ideal decoder $\mathcal D$ and fault-tolerant gadgets satisfying Definitions 2–5, with Pauli faults. A truncated ExRec is an ExRec of type $\kappa$ from which the trailing EC steps on a nonempty set $T$ of output blocks have been removed (Definition 10). Only ExRecs with trailing ECs can be truncated: gate, wait and preparation ExRecs. It is good if the remaining locations contain at most $t$ faults:
--
--   $$
--   s_{\mathrm{lead}} + s_{\mathrm{gadget}} + \sum_{j\notin T} s_{\mathrm{trail},j} \le t .
--   $$
--
--   Then:
--
--   1. the truncated ExRec is correct for the ideal decoder, i.e. diagrams (72)/(73) hold with the removed trailing EC steps deleted;
--   2. for every *-decoder $W$ of $\mathcal D$, the truncated ExRec is correct for $W$ (eq. (83) and its preparation version, with the removed trailing EC steps deleted).
--
--   **Formalization Note** The truncation set is a nonempty `Finset` of output blocks. For a measurement ExRec there are no output blocks, so the hypothesis cannot hold, matching the source.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 38, §5.2, Lemma 3. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro




/-- Gottesman intro p.38, Lemma 3: "A good truncated ExRec is correct for both ideal decoders and
*-decoders." Let `P` be a fault-tolerant protocol (Defs. 2–5). For every ExRec type `κ`, every
nonempty set `trunc` of output blocks whose trailing EC is removed (a truncated ExRec, Def. 10;
measurement ExRecs have no trailing EC, so for them the hypothesis is void), and every Pauli
fault arrangement `F` with at most `t` faults in the remaining locations (good, Def. 10), the
truncated ExRec is correct for the ideal decoder, and it is correct for every *-decoder `W` of
the ideal decoder. -/
theorem good_truncated_exRec_correct (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (F : ExRecFaults κ) (trunc : Finset (Fin κ.trailCount)) (htrunc : trunc.Nonempty)
    (hgood : F.count P trunc ≤ P.t) :
    ExRecCorrect P κ F trunc ∧
      ∀ (σ : ℕ) (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ), IsStarDecoder P.dec W →
        ExRecCorrectStar P W κ F trunc := by
  sorry

end QAlgorithms.GottesmanIntro
