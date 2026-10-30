-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_standard_fidelity_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.standard_fidelity_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:15:39.835696+00:00
-- url     : https://prove2.me/theorems/6fffad81-bf6b-4030-8f33-ab988515b5a5
-- title:
--   Theorem 1.2: standard deterministic PBT asymptotics
-- statement:
--   Fix an integer $d\ge1$ and $\delta>0$. Let $F_d^{\mathrm{std}}(N)$ be the squared entanglement fidelity of the protocol using exactly $N$ maximally entangled $d$-dimensional pairs and the pretty good measurement of their physical port ensemble, completed on its kernel. There are $C>0$ and $N_0\ge1$, depending only on $d,\delta$, such that
--   $$\left|F_d^{\mathrm{std}}(N)-1+\frac{d^2-1}{4N}\right|\le C N^{-3/2+\delta}\qquad(N\ge N_0).$$
--   This specifies the leading standard-protocol error and its remainder.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 4, Theorem 1.2: standard deterministic PBT asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Theorem 1.2, PDF p.4 (restated p.30): the physically constructed EPR/PGM protocol.
Constants may depend on fixed d and delta, never on N. -/
theorem standard_fidelity_expansion (d : ℕ) (hd : 1 ≤ d) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      |standardFidelity d N - (1 - ((d : ℝ)^2 - 1)/(4*(N : ℝ)))| ≤
        C * Real.rpow (N : ℝ) (-(3 : ℝ)/2 + delta) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
