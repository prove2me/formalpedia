-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_npt_distillable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.npt_distillable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:18:05.785829+00:00
-- url     : https://prove2.me/theorems/0ecd23b1-2cc8-40cb-8e27-81635de16506
-- title:
--   Every NPT state is distillable via PPT-preserving channels
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d\ge1$ and let $\rho$ be a density operator with $\rho^\Gamma\not\ge0$. Then for every $0<\eta<1$ there are a positive integer $n$ and a PPT channel $T$ from $n$ copies to two qubits such that
--
--   $$\operatorname{tr}\!\left(P_2 T(\rho^{\otimes n})\right)\ge1-\eta.$$
--
--   The copies are grouped as Alice's registers versus Bob's registers. This is qualitative distillability with vanishing singlet error; no rate is specified.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 2, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.2, Theorem 1 (abstract p.1; conclusion p.3): all finite-dimensional NPT
states are distillable through PPT-preserving channels, in the qualitative many-copy sense.
The single-copy threshold witness is stated separately and is not substituted for this goal. -/
theorem npt_distillable (d : ℕ) (hd : 0 < d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (hnpt : ¬ (gamma rho).PosSemidef) :
    IsPositiveConjugatePPTDistillable rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
