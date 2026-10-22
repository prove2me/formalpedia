-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_continuity_on_face_interiors
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.continuity_on_face_interiors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:39:05.437592+00:00
-- url     : https://prove2.me/theorems/004c2f41-ab03-4abc-8d18-cc265002681e
-- title:
--   Continuity on faithful states and relative face interiors
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Let $\mathcal D$ be the convex set of density matrices on the fixed bipartite space. The restriction of $E_{\mathrm{sq}}$ to the faithful, positive-definite states is continuous. For every convex face $F\subseteq\mathcal D$, $$E_{\mathrm{sq}}\big|_{\operatorname{relint}_{\mathbb R}F}\text{ is continuous}.$$ Relative interior is taken in the real affine span of $F$, and continuity uses the restricted domain. This retains the face statement without asserting continuity from higher-rank strata.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 6, §IV, Proposition 16

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

/-- PDF p.6, Proposition 16: continuous on faithful states and on the relative
interior of every convex face. Intrinsic interior is in the REAL affine span;
the second conclusion concerns a restriction, not approach from other faces. -/
theorem continuity_on_face_interiors :
    ContinuousOn (fun rho : Matrix (A × B) (A × B) ℂ => sq rho)
      {rho | IsDensityMatrix rho ∧ rho.PosDef} ∧
    (∀ F : Set (Matrix (A × B) (A × B) ℂ),
      Convex ℝ F → IsExtreme ℝ {rho | IsDensityMatrix rho} F →
      ContinuousOn (fun rho : Matrix (A × B) (A × B) ℂ => sq rho)
        (intrinsicInterior ℝ F)) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
