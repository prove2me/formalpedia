-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P69_simultaneous_teleportation
-- name    : QAlgorithms.Papers.Independent.Intake100.P69.simultaneous_teleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:26:49.735172+00:00
-- url     : https://prove2.me/theorems/d42109c9-23ed-4ff6-a959-3be2368e9b1d
-- title:
--   One joint port measurement teleports k labeled qubits
-- statement:
--   Let $N\ge1$ and $1\le k\le N$ be integers. Alice and Bob share exactly $N$ normalized qubit singlets. There exists one joint POVM on Alice's $k$ inputs and $N$ port halves, with outcomes the ordered injections $f:\{1,\ldots,k\}\hookrightarrow\{1,\ldots,N\}$. Alice announces $f$ once; Bob retains the selected halves in input order and discards the others. This measurement is independent of the unknown input and Bob applies no correction.
--
--   The induced channel has joint entanglement fidelity
--
--   $$
--   F_{\rm e}(\mathcal P_{\rm sim}(N,k))\ge1-\frac{4k}{N}.
--   $$
--
--   Here joint entanglement fidelity is the singlet overlap of reference and ordered outputs when the inputs are halves of $k$ normalized singlets. It is computed by summing the subnormalized joint measurement branches and tracing out Alice and the unused Bob ports. The result retains the printed finite qubit bound, including the regime where its right-hand side is nonpositive.
-- source:
--   Generalized teleportation and entanglement recycling, arXiv:1209.2683v2, PDF p. 4, Theorem 2, eq. (6): simultaneous teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P69

namespace QAlgorithms.Papers.Independent.Intake100.P69

open scoped ComplexConjugate

open Filter

/-- PDF p.4, Theorem 2, (6), and pp.10-11: for every admissible qubit input
count there exists one joint POVM over ordered distinct assignments, independent
of the unknown input, attaining the finite joint entanglement-fidelity bound. -/
theorem simultaneous_teleportation (N k : ℕ) (hN : 1 ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ M : SimMeasurement N k, IsPOVM M ∧
      1 - 4 * (k : ℝ) / (N : ℝ) ≤ simultaneousFidelity M := by sorry

end QAlgorithms.Papers.Independent.Intake100.P69
