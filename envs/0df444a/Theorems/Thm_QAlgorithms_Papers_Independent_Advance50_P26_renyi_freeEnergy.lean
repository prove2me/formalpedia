-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P26_renyi_freeEnergy
-- name    : QAlgorithms.Papers.Independent.Advance50.P26.renyi_freeEnergy
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:40:43.365985+00:00
-- url     : https://prove2.me/theorems/765939cf-ff05-448e-9c9c-ef332040f244
-- title:
--   Renyi entropy is the negative temperature secant slope of free energy
-- statement:
--   Let $H$ be a self-adjoint complex matrix on a nonzero finite-dimensional space, and let $k>0$ be Boltzmann's constant. For each positive temperature $u$, define
--   $$
--   Z_H(k,u)=\operatorname{tr}\exp(-H/(ku)),\qquad
--   \rho_H(k,u)=\frac{\exp(-H/(ku))}{Z_H(k,u)},\qquad
--   F_H(k,u)=-ku\ln Z_H(k,u).
--   $$
--   For a density matrix $\rho$ and a real order $q>0$, $q\ne1$, define its Renyi entropy by $S_q^k(\rho)=k\ln\operatorname{tr}(\rho^q)/(1-q)$, where the power is spectral and all logarithms are natural. For any positive temperatures $T_0,T$ with $T\ne T_0$, one has
--   $$
--   S_{T_0/T}^k\bigl(\rho_H(k,T_0)\bigr)
--   =-\frac{F_H(k,T)-F_H(k,T_0)}{T-T_0}.
--   $$
--   This relates entropy at the original temperature to an equilibrium free-energy difference for the same Hamiltonian and Boltzmann constant. No positivity condition on $H$ or zero-reference-free-energy condition is required.
-- source:
--   Renyi Entropy and Free Energy, arXiv:1102.2098v4, PDF p. 1, Abstract; Section 2, Eq. (9), PDF p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P26

noncomputable section

open Filter

open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P26

open QAlgorithms.Papers.Independent.Support50.P15 (shannonEntropyNats)

open QAlgorithms.ZeroSum (classicalGibbs)

open QAlgorithms.Papers.Independent.Dependency50.P35 (spectralPower)

/-- PDF p.3, Section 2, (8)-(9): the entropy of the Gibbs state at T0 is the
negative secant slope of free energy between T0 and T. Here q is constructed as T0/T;
positive distinct temperatures ensure q > 0 and q != 1. No hypothesis F(T0) = 0 or
H positive semidefinite is imposed. The p.3 source corrections are documented above. -/
theorem renyi_freeEnergy {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (k T0 T : ℝ) (hk : 0 < k) (hT0 : 0 < T0) (hT : 0 < T) (hneq : T ≠ T0) :
    renyiEntropyWithBoltzmann (thermalGibbs H k T0) k (T0 / T) =
      -(thermalFreeEnergy H k T - thermalFreeEnergy H k T0) / (T - T0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P26

end
