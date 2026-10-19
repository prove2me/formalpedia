-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_singleEnvironmentClassification
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.singleEnvironmentClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:17:43.235134+00:00
-- url     : https://prove2.me/theorems/465e5405-6361-4040-aba7-e655798ff668
-- title:
--   Single-environment Gaussian-channel threshold classification
-- statement:
--   Let $U$ be a bounded joint unitary on two complete single-mode Fock spaces and let $\sigma$ be a possibly mixed Gaussian environmental density. Suppose $U$ implements the full linear canonical transformation $U(a,a^\dagger,b,b^\dagger)^T U^\dagger=A(a,a^\dagger,b,b^\dagger)^T$, including conjugacy and all canonical commutators. Write $q=|A_{11}|^2-|A_{12}|^2$. Let $E$ and $\widetilde E$ be the receiver and environmental partial traces of $U(\rho\otimes\sigma)U^\dagger$. Then
--
--   $$
--   q\ge\tfrac12\ \Longrightarrow\ E\text{ is weakly degradable},\qquad
--   q\le\tfrac12\ \Longrightarrow\ E\text{ is anti-degradable}.
--   $$
--
--   Each recovery is a full trace-class CPTP map chosen before every input density. The assertions include $q=0,1$ and overlap at $q=1/2$. This classifies precisely the stipulated single-environment representations, without an energy cutoff.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 3, §III, Table I; q=0,1 on p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section III/Table I, PDF p.3 (q=0,1 discussed on p.4 with [24]): the full
single-environment classification. Scope is the stipulated canonical dilation,
not every Gaussian channel. At q=1/2 both implications apply. -/
theorem singleEnvironmentClassification
    (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (A : Matrix (Fin 4) (Fin 4) ℂ)
    (sigma : State ℕ) (hcanonical : Canonical U A)
    (hgaussian : GaussianDensity sigma.coefficients) :
    ((1 / 2 : ℝ) ≤ characteristicQ A →
      WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) ∧
    (characteristicQ A ≤ (1 / 2 : ℝ) →
      AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
