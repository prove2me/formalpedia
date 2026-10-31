-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P57_port_teleportation_diamond
-- name    : QAlgorithms.Papers.Independent.Intake100.P57.port_teleportation_diamond
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:57:43.705235+00:00
-- url     : https://prove2.me/theorems/297aa2db-d5b5-4eb3-8083-010db9e6fa7d
-- title:
--   Port-based teleportation: a uniform diamond-distance bound
-- statement:
--   Let $d,N\ge1$ be integers. Alice holds a $d$-dimensional input $A$, and Alice and Bob share exactly $N$ copies of $|\Phi_d\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle$ in registers $A_i',B_i'$. There is a single $N$-outcome POVM on $AA_1'\cdots A_N'$, chosen independently of the unknown input, such that the following channel $\mathcal E$ is CPTP: Alice measures this POVM and sends its outcome $i$ to Bob; Bob discards every port except $B_i'$ and identifies that port with the output. No correction on the retained port is performed. Then
--
--   $$
--   \|\mathcal E-\mathrm{id}_d\|_\diamond\le\frac{4d^2}{\sqrt N}.
--   $$
--
--   The diamond norm is the full completely bounded trace norm, with no factor $1/2$, so the estimate includes inputs entangled with arbitrary reference registers. This is the source's worst-case port-teleportation guarantee.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, PDF p. 7, II.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.

open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)

open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/-- Corollary II.2, PDF p.7, using the exact operation (5) on p.6.
The same POVM is fixed before every input and entangled reference. -/
theorem port_teleportation_diamond (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    ∃ E : Fin N → Matrix (Fin d × (Fin N → Fin d))
      (Fin d × (Fin N → Fin d)) ℂ,
      IsPOVM E ∧ IsChannel (pbtChannel E) ∧
      2 * diamondDistance (pbtChannel E) (fun X => X) ≤
        4 * (d : ℝ)^2 / Real.sqrt (N : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P57

end
