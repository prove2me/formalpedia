-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_lemma_31
-- name    : PrivPACLower.ICP.Supplement.lemma_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:18:40.154306+00:00
-- url     : https://prove2.me/theorems/4ca91512-4de4-432a-bdd4-d5e742511178
-- title:
--   Lemma 31 (used in the proof of Theorem 11) — private release of all threshold queries
-- statement:
--   There is a universal constant $C\ge2$ such that the following holds. Let $M\ge2$, $0<\varepsilon\le1$ and $0<\delta,\eta,\zeta\le1/4$. For a database $T=(z_1,\dots,z_n)\in[M]^n$ let $F_T(t)=\frac1n\sum_{i=1}^n\mathbf 1\{z_i\le t\}$ for $t\in\{0,\dots,M\}$, and $\ell_M=\log^*(\max\{2,M\})$. If
--   $$n\ge\frac{C}{\varepsilon\eta}\Bigl[\ell_M\log^2\Bigl(\frac{C\ell_M}{\eta\zeta\delta}\Bigr)+\log\Bigl(\frac C\zeta\Bigr)\log^{5/2}\Bigl(\frac C\eta\Bigr)\Bigr],\tag{21}$$
--   then there is an $(\varepsilon,\delta)$-DP algorithm that on every database $T\in[M]^n$ returns answers $\widehat F(0),\dots,\widehat F(M)$ with
--   $$\Pr\Bigl[\max_{0\le t\le M}\bigl|\widehat F(t)-F_T(t)\bigr|\le\eta\Bigr]\ge1-\zeta.$$
--
--   All $M+1$ threshold queries are answered simultaneously; this is the private subroutine of the interval-union learner.
--
--   **Formalization Note** The output is a vector in $\mathbb R^{M+1}$ with its Borel product sigma-algebra; logarithms are natural.
--
--   Differences from the source:
--   - encoding: a randomized algorithm on databases in [M]^n returning M+1 answers → a Mechanism from Fin n -> Fin M to probability measures on Fin (M+1) -> R, DP for Borel-measurable events; reason: every event of the source's answers that is used is Borel; replacement adjacency as in the base mission
--   - encoding: [M] = {1, ..., M} and t in {0, ..., M} → Fin M with z standing for z + 1, and t : Fin (M + 1); reason: bijective relabelling; no instance changes
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 48, Lemma 31 (proof p. 48). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Supplement_Basics
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem lemma_31 :
    ∃ C : ℝ, 2 ≤ C ∧
      ∀ M : ℕ, 2 ≤ M → ∀ ε δ η ζ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1/4 →
        0 < η → η ≤ 1/4 → 0 < ζ → ζ ≤ 1/4 →
        ∀ n : ℕ,
          C / (ε * η) * (ellStar M * Real.log (C * ellStar M / (η * ζ * δ)) ^ 2 +
            Real.log (C / ζ) * Real.log (C / η) ^ (5/2 : ℝ)) ≤ n →
          ∃ A : Mechanism (Fin M) (Fin (M + 1) → ℝ) n, IsDP A ε δ ∧
            ∀ T : Fin n → Fin M,
              ENNReal.ofReal (1 - ζ) ≤
                (A T : Measure (Fin (M + 1) → ℝ))
                  {F | ∀ t : Fin (M + 1), |F t - thresholdCDF T t.val| ≤ η} := by sorry

end PrivPACLower.ICP.Supplement
