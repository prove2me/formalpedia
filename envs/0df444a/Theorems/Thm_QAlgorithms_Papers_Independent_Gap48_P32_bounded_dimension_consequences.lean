-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_bounded_dimension_consequences
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.bounded_dimension_consequences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:36:18.07625+00:00
-- url     : https://prove2.me/theorems/381e77d1-0438-41fe-a979-24d1aa1b8567
-- title:
--   Consequences of a uniform extension dimension bound
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Fix the bipartite space. Suppose one positive integer $d$, chosen before the state, has the following property: for every state $\rho$ and every finite extension $\omega$ of $\rho$, there is an extension $\tau$ on a $d$-dimensional environment with $I(A;B|E)_\tau\le I(A;B|E)_\omega$. Then every state has such an extension attaining $$E_{\mathrm{sq}}(\rho)=\tfrac12 I(A;B|E)_\tau.$$ Also $E_{\mathrm{sq}}$ is continuous on the full state set and $$E_{\mathrm{sq}}(\rho)=0\quad\Longleftrightarrow\quad\rho\text{ is separable}.$$ This is a conditional compactness consequence; no dimension bound is asserted to exist.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 6, §IV, conditional extension-bound paragraph

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

/-- PDF p.6, conditional dimension-bound paragraph: one common d implies
attainment, continuity on the full state set, and zero iff separability.
The printed reference to "remark 7" refers to Theorem 7. -/
theorem bounded_dimension_consequences (d : ℕ) (hd : 0 < d)
    (hbound : UniformExtensionBound (A := A) (B := B) d) :
    (∀ rho : Matrix (A × B) (A × B) ℂ, IsDensityMatrix rho →
      ∃ omega : Matrix ((A × B) × Fin d) ((A × B) × Fin d) ℂ,
        IsDensityMatrix omega ∧ traceRight omega = rho ∧ sq rho = cmi omega / 2) ∧
    ContinuousOn (fun rho : Matrix (A × B) (A × B) ℂ => sq rho)
      {rho | IsDensityMatrix rho} ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, IsDensityMatrix rho →
      (sq rho = 0 ↔ Entanglement.IsSeparableDensity rho)) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
