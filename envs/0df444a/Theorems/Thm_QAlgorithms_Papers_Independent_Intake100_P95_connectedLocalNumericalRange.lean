-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_connectedLocalNumericalRange
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.connectedLocalNumericalRange
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:58:58.315653+00:00
-- url     : https://prove2.me/theorems/a12cd6eb-d617-4841-b0e2-5c1fd787e43c
-- title:
--   Connected local C-numerical ranges and the reversible interval
-- statement:
--   Let $n\ge1$. For arbitrary complex operators $A,C$ on $n$ qubits define
--
--   $$W_{\mathrm{loc}}(C,A)=\{\operatorname{tr}(C^\dagger KAK^\dagger):K\in\mathrm{SU}(2)^{\otimes n}\}.$$
--
--   This set is compact and connected. When $A$ and $C$ are Hermitian it is an attained real interval $[a,b]$, viewed inside the complex plane. If $H$ is Hermitian and traceless, $\|H\|_F=1$, and $H$ is type-I reversible, then $W_{\mathrm{loc}}(-H,H)=[-1,1]$. The one-way interval assertion is retained without the erroneous endpoint equivalence printed in Corollary 3.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 12, (69): connected local C-numerical range

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (69), PDF p.12: the local C-numerical range is connected for arbitrary
complex matrices; Hermiticity gives a real attained interval. The reversible
normalized case gives the full [-1,1]. The erroneous converse endpoint of
Corollary 3 is deliberately not asserted. -/
theorem connectedLocalNumericalRange {n : ℕ} (hn : 0 < n) :
    (∀ C A : Op (QAlgorithms.Qubits n), IsCompact (localNumericalRange C A) ∧
      IsConnected (localNumericalRange C A)) ∧
    (∀ C A : Op (QAlgorithms.Qubits n), C.IsHermitian → A.IsHermitian →
      ∃ lo hi : ℝ, lo ≤ hi ∧
        localNumericalRange C A = {z : ℂ | z.im = 0 ∧ lo ≤ z.re ∧ z.re ≤ hi}) ∧
    (∀ H : Op (QAlgorithms.Qubits n), IsHamiltonian H → QAlgorithms.frobNorm H = 1 → TypeI H →
      localNumericalRange (-H) H = {z : ℂ | z.im = 0 ∧ -1 ≤ z.re ∧ z.re ≤ 1}) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
