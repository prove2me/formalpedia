-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_fourDimensionalSeparation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.fourDimensionalSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:44:59.273803+00:00
-- url     : https://prove2.me/theorems/02125f8d-bede-4213-987b-f7ab2dee2512
-- title:
--   An explicit four-dimensional single-input private/coherent separation
-- statement:
--   On a four-dimensional register with basis $|1\rangle,\ldots,|4\rangle$, let $\Pi_{12}$ and $\Pi_{34}$ be the orthogonal rank-two block projectors, put $\pi_{12}=\Pi_{12}/2$, $\pi_{34}=\Pi_{34}/2$, and define
--
--   $$\mathcal N(\rho)=\Pi_{12}\rho\Pi_{12}+\operatorname{Tr}(\Pi_{34}\rho\Pi_{34})\pi_{34}.$$
--
--   Use the explicit five-Kraus dilation consisting of $\Pi_{12}$ and $|a\rangle\langle b|/\sqrt2$ for $a,b\in\{3,4\}$. It is an isometry and its receiver channel is exactly $\mathcal N$. In bits, $I_c(\pi_{12},\mathcal N)=1$ and $I_c(\pi_{34},\mathcal N)=-1$.
--
--   There is $\epsilon_0\in(0,1/2]$ such that for every $0<\epsilon<\epsilon_0$, both $\pi'_{12}=(1-\epsilon)\pi_{12}+\epsilon\pi_{34}$ and $\pi'_{34}=(1-\epsilon)\pi_{34}+\epsilon\pi_{12}$ are density matrices, $I_c(\pi'_{34},\mathcal N)<0$, and
--
--   $$I_p(\pi'_{12},\mathcal N)>I_c(\pi'_{12},\mathcal N)>0.$$
--
--   This is a concrete separation of information at a specified input, not a strict separation of optimized asymptotic capacities.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 18, Appendix C / (56)–(57)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Appendix C, PDF pp.17–18: the concrete four-dimensional channel and the
specified perturbed states have Ip>Ic>0. This separates single-input information,
not the optimized capacities. Unperturbed values and the negative component
are included, and the dilation's channel identity is a conclusion. -/
theorem fourDimensionalSeparation :
    IsDilation separationDilation ∧ receiver separationDilation = separationChannel ∧
    coherentInformation (receiver separationDilation) pi12 = 1 ∧
    coherentInformation (receiver separationDilation) pi34 = -1 ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 2 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      IsDensityMatrix (perturbed12 eps) ∧ IsDensityMatrix (perturbed34 eps) ∧
      0 < coherentInformation (receiver separationDilation) (perturbed12 eps) ∧
      coherentInformation (receiver separationDilation) (perturbed34 eps) < 0 ∧
      coherentInformation (receiver separationDilation) (perturbed12 eps) <
        privateInformation separationDilation (perturbed12 eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
