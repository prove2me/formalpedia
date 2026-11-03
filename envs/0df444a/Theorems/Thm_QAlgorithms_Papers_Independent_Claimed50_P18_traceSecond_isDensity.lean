-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_traceSecond_isDensity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.traceSecond_isDensity
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-02T20:16:12.677676+00:00
-- url     : https://prove2.me/theorems/6a27e376-f75e-4a64-b650-38373ab347dc
-- title:
--   The partial trace of a density operator is a density operator
-- statement:
--   Let $\mathcal H_I,\mathcal H_J$ be separable complex Hilbert spaces with countable orthonormal bases indexed by $I$ and $J$, and let $ho$ be a density operator (positive trace-class operator of trace one) on $\mathcal H_I\otimes\mathcal H_J$. Then its reduced state
--
--   $$
--   ho_I=\operatorname{Tr}_Jho,\qquad (ho_I)_{ii'}=\sum_{j\in J}ho_{(i,j),(i',j)},
--   $$
--
--   is a density operator on $\mathcal H_I$. In the source this makes $ho_{AB}=\operatorname{Tr}_Cho_{ABC}$ a legitimate input state for the channels $\operatorname{Tr}_B,\operatorname{Tr}_A$ in (3)-(4).
--
--   **Formalization Note** Density operators are the frozen `IsDensity` of Dependency50.P33 (nuclear trace class, real nonnegative finite quadratic forms, summable real diagonal of sum $1$); the partial trace is `traceSecond` of Frontier18.P01.
-- source:
--   Kuznetsova, Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, identities (3)-(4) (rho_AB as input state); Holevo, Quantum Systems, Channels, Information (2nd ed.), Section 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

theorem traceSecond_isDensity {I J : Type} [Countable I] [Countable J] (rho : State (I × J)) :
    IsDensity (traceSecond rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
