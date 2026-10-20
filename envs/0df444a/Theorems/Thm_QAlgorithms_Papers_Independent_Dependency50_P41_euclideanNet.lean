-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_euclideanNet
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.euclideanNet
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:58:38.093195+00:00
-- url     : https://prove2.me/theorems/02e0c494-b4d9-440f-8ead-30dafa0b15c2
-- title:
--   Finite Euclidean net with centers in the prescribed set
-- statement:
--   Let $d\ge1$, $D>0$ and $0<\varepsilon<1$. Let $T\subseteq\{v\in\mathbb C^d:\|v\|_2\le D\}$. Then a finite subset $T_\varepsilon\subseteq T$ exists such that $$|T_\varepsilon|\le\left(\frac{2D}{\varepsilon}+1\right)^{2d},\qquad\forall v\in T\;\exists w\in T_\varepsilon:\|v-w\|_2\le\varepsilon.$$ The empty set $T$ is permitted.
--
--   The exponent uses the real dimension of $\mathbb C^d$, and all net centers lie in the original set.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 22, Lemma 37

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF p.22, Lemma 37.
Centers belong to T; T may be empty. The exponent is the real dimension 2*d. -/
theorem euclideanNet (d : ℕ) (hd : 0 < d) (D epsilon : ℝ)
    (hD : 0 < D) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (T : Set (EuclideanSpace ℂ (Fin d))) (hT : ∀ v ∈ T, ‖v‖ ≤ D) :
    ∃ net : Finset (EuclideanSpace ℂ (Fin d)),
      (∀ w ∈ net, w ∈ T) ∧
      (net.card : ℝ) ≤ (2 * D / epsilon + 1) ^ (2 * d) ∧
      ∀ v ∈ T, ∃ w ∈ net, ‖v - w‖ ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
