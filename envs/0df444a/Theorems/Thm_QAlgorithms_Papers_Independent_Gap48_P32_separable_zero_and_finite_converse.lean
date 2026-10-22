-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_separable_zero_and_finite_converse
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.separable_zero_and_finite_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:30:42.535861+00:00
-- url     : https://prove2.me/theorems/cdbf417d-f1a3-48b3-8101-3f95c68af00a
-- title:
--   Separable zero value and finite zero-CMI converse
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   For every state $\rho^{AB}$, $$\rho\text{ separable}\ \Longrightarrow\ E_{\mathrm{sq}}(\rho)=0.$$ Conversely, $$\bigl[\exists\text{ finite extension }\omega^{ABE}:I(A;B|E)_\omega=0\bigr]\ \Longrightarrow\ \rho\text{ separable}.$$ Here separability means a finite convex combination of product density matrices. This retains the finite-extension converse without assuming the infimum is attained.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 3, §II, Theorem 7 (continued p.4)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

section Bipartite

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [instAne : Nonempty A] [instBne : Nonempty B]

include instAne instBne

/-- PDF pp.3--4, Theorem 7: only an ACTUAL finite zero-CMI extension supplies
the converse. No attainment is assumed for the unrestricted infimum. -/
theorem separable_zero_and_finite_converse (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    (Entanglement.IsSeparableDensity rho → sq rho = 0) ∧
    ((∃ e : ℕ, 0 < e ∧
      ∃ omega : Matrix ((A × B) × Fin e) ((A × B) × Fin e) ℂ,
        IsDensityMatrix omega ∧ traceRight omega = rho ∧ cmi omega = 0) →
      Entanglement.IsSeparableDensity rho) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
