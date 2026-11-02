-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_arbitrarily_long_range
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.arbitrarily_long_range
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:09:24.31584+00:00
-- url     : https://prove2.me/theorems/17950c13-3289-41f1-b42e-871f033be9b9
-- title:
--   Abstract and conclusions: arbitrarily long-range two-point correlations
-- statement:
--   For every $N\ge2$, there are bond-one periodic tensors $A$, admissible weighted graph data $\Phi$, and local unitaries $V_k\in U(2)$ for which the RAGE raw vector $v$ is nonzero. Its normalization $\psi=v/\|v\|$ is a unit vector and has
--
--   $$\langle Z_1Z_N\rangle_\psi-\langle Z_1\rangle_\psi\langle Z_N\rangle_\psi=1.$$
--
--   Here $Z_k$ is the Pauli $Z$ operator on site $k$, with eigenvalues $+1,-1$ on computational bits $0,1$. The endpoints have chain distance $N-1$. This is an existential expressiveness statement for arbitrarily large distances.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 1, Abstract and conclusions: arbitrarily long-range two-point correlations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- Abstract PDF p.1 and conclusions p.4: correlations need not decay with separation.
A phase-π edge between the first and last sites and a Hadamard at one endpoint gives a Bell pair. -/
theorem arbitrarily_long_range (N : ℕ) (hN : 2 ≤ N) :
    ∃ (A : Tensors N 1) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ),
      rage A G V ≠ 0 ∧ IsState (normalizeRageVector (rage A G V)) ∧
      connectedZ (normalizeRageVector (rage A G V)) ⟨0, by omega⟩ ⟨N - 1, by omega⟩ = 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
