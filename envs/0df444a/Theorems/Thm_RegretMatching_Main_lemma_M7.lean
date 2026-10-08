-- Prove2me | Theorems.Thm_RegretMatching_Main_lemma_M7
-- name    : RegretMatching.Main.lemma_M7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:33.332285+00:00
-- url     : https://prove2.me/theorems/fbf4c0a7-fefb-4c25-a7e9-65863a0e7895
-- title:
--   LEMMA (proof of Step M7), p. 1148 — a stochastic matrix with positive diagonal has [Π^{w+1} − Π^w](j,k) = O(w^{−1/2})
-- statement:
--   For every $\beta>0$ there is a constant $C$ such that for every $m$ and every $m\times m$ stochastic matrix $\Pi$ whose diagonal entries are all at least $\beta$,
--   $$\big|[\Pi^{w+1}-\Pi^{w}](j,k)\big|\le\frac{C}{\sqrt w}\qquad\text{for all }w\ge1\text{ and all }j,k=1,\dots,m .$$
--
--   The paper's LEMMA: if $\Pi$ is a stochastic matrix with all diagonal entries positive, then $[\Pi^{w+1}-\Pi^w](j,k)=O(w^{-1/2})$. Consecutive powers of a lazy chain become close even without convergence of the powers.
--
--   **Formalization Note.** This is a disclosed strengthening of the literal statement: the constant depends only on a lower bound $\beta$ on the diagonal, not on the matrix itself. The paper's proof yields exactly this ("Let $\beta>0$ be a lower bound on all the diagonal entries"), and Step M7 needs it, because $\Pi_t$ varies with $t$ while its diagonal stays above $1-2M(m-1)/\mu$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1148, Appendix, proof of Step M7, LEMMA; proof pp. 1148–1149

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem lemma_M7 :
    ∀ β : ℝ, 0 < β → ∃ C : ℝ, ∀ (m : ℕ) (Pi_ : Matrix (Fin m) (Fin m) ℝ),
      (∀ j k, 0 ≤ Pi_ j k) → (∀ j, ∑ k, Pi_ j k = 1) → (∀ j, β ≤ Pi_ j j) →
      ∀ w : ℕ, 1 ≤ w → ∀ j k, |(Pi_ ^ (w + 1) - Pi_ ^ w) j k| ≤ C / Real.sqrt w := by sorry

end RegretMatching.Main
