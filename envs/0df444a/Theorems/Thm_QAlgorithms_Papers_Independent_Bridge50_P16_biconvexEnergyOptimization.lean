-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_biconvexEnergyOptimization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.biconvexEnergyOptimization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:48:14.256864+00:00
-- url     : https://prove2.me/theorems/32f8b923-8bc4-4100-9236-ad21b36cbfc5
-- title:
--   Section V C, Eq.(67): energy-constrained joint encoding/decoding is biconvex
-- statement:
--   Fix $1\le d\le n$, an $n$-dimensional CPTP noise map $\mathcal N$, a Hermitian energy observable $H$, and a real budget $B$ for which at least one encoding is feasible. Let $X_E$ and $X_D$ be unnormalized input-first encoding and decoding Choi matrices. The feasible sets are
--
--   $$\mathcal E_B=\{X_E\succeq0:\operatorname{Tr}_{\rm out}X_E=I_d,\ \operatorname{Tr}[(I_d\otimes H)X_E]\le Bd\},\quad\mathcal D=\{X_D\succeq0:\operatorname{Tr}_{\rm out}X_D=I_n\}.$$
--
--   Both are convex, and the objective $\operatorname{Re}\operatorname{Tr}[X_D f_{\mathcal N}(X_E)]$ is real bilinear, hence linear when either variable is fixed. Here $f_{\mathcal N}$ is the contraction of Eq.(64), equivalently the linear map defined by $f_{\mathcal N}(X)[(l',i'),(l,i)]=\sum_{k,k'}X_{\mathcal N}[(k,l),(k',l')]X[(i,k),(i',k')]$. The energy functional satisfies
--
--   $$\operatorname{Tr}[(I_d\otimes H)X_E]=d\operatorname{Tr}[H\mathcal E(I_d/d)].$$
--
--   The joint maximum is attained for some feasible pair. Thus each fixed-variable problem has semidefinite constraints and a linear objective. This concerns the encoded maximally mixed state and gives no convergence guarantee for alternating optimization.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 13, Section V C, Eq.(67): energy-constrained joint encoding/decoding is biconvex

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- PDF pp.12--13 Eq.(67): separately convex feasible Choi sets and linear
SDP slices. Printed H tensor I has swapped wires; changed to I_d tensor H
because Eq.(63)'s E Choi is input-first. Energy is only that of E(I_d/d).
No global convergence of alternating SDP is asserted. -/
theorem biconvexEnergyOptimization {d n : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (N : Superop (Fin n) (Fin n)) (hN : IsChannel N)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (budget : ℝ)
    (hfeasible : (feasibleEncoding d n H budget).Nonempty) :
    Convex ℝ (feasibleEncoding d n H budget) ∧
    Convex ℝ {XD : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ | CPTP XD} ∧
    (∀ XE, encodingEnergy H XE = (d : ℝ) *
      (H * applyChoi XE (((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ))).trace.re) ∧
    (∃ L : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ →ₗ[ℝ]
        (Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ →ₗ[ℝ] ℝ),
      ∀ XE XD, L XE XD = jointObjective N XE XD) ∧
    (∃ XE ∈ feasibleEncoding d n H budget,
      ∃ XD : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ, CPTP XD ∧
        ∀ YE ∈ feasibleEncoding d n H budget,
          ∀ YD : Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ, CPTP YD →
            jointObjective N YE YD ≤ jointObjective N XE XD) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
