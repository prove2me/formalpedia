-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_unassisted_in_cpp
-- name    : QAlgorithms.Papers.Independent.Support50.P04.unassisted_in_cpp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:32:11.575324+00:00
-- url     : https://prove2.me/theorems/cc4e2291-8516-4fc0-8256-39b51e07289f
-- title:
--   Unassisted codes embed in cpp codes
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. For every actual unassisted encoder/decoder code $C$ for one possibly blocked channel $\mathcal N$, there is an actual cpp code $D$ with
--
--   $$\dim Q_D=1,\qquad M_D=M_C,\qquad F(\mathcal N,D)=F(\mathcal N,C).$$
--
--   Thus every feasible unassisted rate/error pair remains feasible with cpp assistance.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 10, §III.B, final paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.10: every actual unassisted code is a cpp code
with one-dimensional sender memory, preserving the SAME message size and fidelity. -/
theorem unassisted_in_cpp [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (C : QAlgorithms.Papers.Independent.Information100.P80.TransmissionCode A B) :
    ∃ D : CppCode A B, D.q = 1 ∧ D.M = C.M ∧
      cppFidelity N D = QAlgorithms.Papers.Independent.Information100.P80.transmissionFidelity N C := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
