-- Prove2me | Theorems.Thm_RegretMatching_Main_piMat_stochastic_diag_pos
-- name    : RegretMatching.Main.piMat_stochastic_diag_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:22.740397+00:00
-- url     : https://prove2.me/theorems/237d1144-57cc-48eb-a619-105857f3f772
-- title:
--   §2 p. 1130 and Appendix p. 1144 — under footnote 5's μ, each row of Π_t is a probability vector with Π_t(j,j) ≥ 1 − 2M(m−1)/μ > 0
-- statement:
--   Let $\Gamma$ be a finite game, let $M^i$ bound $|u^i|$ for every player $i$, and let $\mu>2M^i(m^i-1)$ for every $i$, where $m^i=|S^i|$ (footnote 5). Then for every player $i$, every $t\ge1$, every history $h_t$ and every $j\in S^i$, the row $\Pi^i_t(j,\cdot)$ of the regret-matching matrix (2.2) is a probability vector on $S^i$, and its diagonal entry satisfies
--   $$\Pi^i_t(j,j)\ \ge\ 1-\frac{2M^i(m^i-1)}{\mu}\ >\ 0 .$$
--
--   This is the content of "the choice of $\mu$ guarantees that $p^i_{t+1}(j)>0$" (p. 1130) and "$\Pi_t(j,j)>0$ for all $j$ and all $t$" (p. 1144). It makes (2.2) a well-defined mixed action, and the uniform lower bound on the diagonal is what the Step M7 estimate needs.
--
--   **Formalization Note.** The explicit bound $1-2M^i(m^i-1)/\mu$ is the uniform form of "$>0$" (it follows from $|D^i_t|\le 2M^i$); it is stated because the uniformity in $t$ is used later.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1130, §2, (2.2) and footnote 5; p. 1144, Appendix (Π_t(j,j) > 0)

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem piMat_stochastic_diag_pos
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) {t : ℕ} (ht : 1 ≤ t) (h : Fin t → (∀ i, S i)) :
    (∀ j : S i, PiMat u μ h i j ∈ stdSimplex ℝ (S i)) ∧
      ∀ j : S i, 1 - 2 * M i * ((Fintype.card (S i) : ℝ) - 1) / μ ≤ PiMat u μ h i j j ∧
        0 < PiMat u μ h i j j := by sorry

end RegretMatching.Main
