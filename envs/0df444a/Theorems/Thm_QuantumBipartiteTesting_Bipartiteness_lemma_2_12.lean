-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_12
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:12:29.29662+00:00
-- url     : https://prove2.me/theorems/2a942e33-53d8-47b6-bb35-c974a11d150f
-- title:
--   Lemma 2.12 — translated bivariate grid degree bound
-- statement:
--   For each fixed $\gamma>0$ there is a constant $c(\gamma)>0$. For every positive integer center $C$, integer radius $R\ge2$, and real bivariate polynomial $Q$, assume
--   $$|Q(X,\ell)|\le1\quad\text{for integer }1\le\ell\le R,\quad|X-C|\le R^{3/2}/2,\quad\ell\mid X.$$
--   If $|Q(C,1)-Q(C,2)|\ge\gamma$, then
--   $$\deg Q\ge c(\gamma)\sqrt R.$$
--   The constant precedes and is independent of the center, radius and polynomial. The integer grid includes every integer horizontal coordinate satisfying the displayed conditions. This is the translated degree obstruction invoked after rescaling $M=2X$.
--
--   Differences from the source:
--   - encoding: positive integers C,R and an arithmetic grid with integer X,l → C,R are naturals with explicit positivity/radius conditions; X,l range over integers; reason: preserves the full arithmetic grid, the exact half-width, and the dependence only on gamma
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 2.12, PDF = printed page 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_2_12 : ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
    ∀ C R : ℕ, 0 < C → 2 ≤ R → ∀ Q : Bivariate,
      (∀ X l : ℤ, 1 ≤ l → l ≤ (R : ℤ) →
        |(X : ℝ) - C| ≤ (R : ℝ)^(3/2 : ℝ)/2 → l ∣ X → |Eval Q X l| ≤ 1) →
      γ ≤ |Eval Q C 1 - Eval Q C 2| → c * Real.sqrt R ≤ (Q.totalDegree : ℝ) := by sorry

end QuantumBipartiteTesting.Bipartiteness
