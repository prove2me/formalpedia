-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_allOutputEntropyConstraint
-- name    : QAlgorithms.Papers.Independent.Information100.P22.allOutputEntropyConstraint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:52:54.989994+00:00
-- url     : https://prove2.me/theorems/8822800b-0355-4585-bcce-0129155d4fe9
-- title:
--   Proposition 3: Architecture-independent all-output constraint
-- statement:
--   Let $m\ge2$, $k\ge1$, and let $R$ be any normalized pure resource on $mk$ signal and $mk$ key qubits. Let $U$ be an arbitrary unitary on $AS$, leaving $N$ untouched. If every $S_iN$ exactly recovers the full input through a fixed CPTP map, then
--   $$S(\rho_N)=(m-1)k+S(\Omega_A)\ge(m-1)k.$$
--   Entropies are in bits and $\Omega_A$ is the transformed source marginal at the maximally mixed Choi input. Also every individual signal channel is $X\mapsto\operatorname{Tr}(X)I/2^k$. This is independent of graph, stabilizer, Pauli, or concealment assumptions.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 5, Proposition 3: Architecture-independent all-output constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Proposition 3, PDF pp.5–6, proof pp.26–28: arbitrary unitary encoder on AS. -/
theorem allOutputEntropyConstraint (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ)
    (hrec : AllRecoverable R (U : Op _)) :
    vnEntropy (rhoN R) = (((m-1)*k : ℕ) : ℝ) + vnEntropy (sourceMarginal R (U : Op _)) ∧
    (((m-1)*k : ℕ) : ℝ) ≤ vnEntropy (rhoN R) ∧
    UniformlyConcealed R (U : Op _) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
