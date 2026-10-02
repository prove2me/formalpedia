-- Prove2me | Theorems.Thm_StochFictPlay_Potential_lemmaA5_exists_player
-- name    : StochFictPlay.Potential.lemmaA5_exists_player
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:13:04.35004+00:00
-- url     : https://prove2.me/theorems/e17744f2-5469-49ee-804a-8eb4c279d52a
-- title:
--   Lemma A.5 — a unit tangent vector has a player whose block spreads by more than $1/(n^\beta\sqrt p)$ on both sides
-- statement:
--   Let $p \ge 2$ players have $n^\alpha \ge 1$ strategies each, and let
--   $$U = \Big\{\theta \in \textstyle\prod_\alpha \mathbb R^{n^\alpha}_0 : \sum_\alpha\sum_i (\theta^\alpha_i)^2 = 1\Big\}$$
--   be the set of unit vectors in the tangent space of $\Sigma$. If $\theta \in U$, then there is a player $\beta$ with
--   $$\max_{i\in S^\beta}\theta^\beta_i > \frac{1}{n^\beta\sqrt p}\qquad\text{and}\qquad \min_{i\in S^\beta}\theta^\beta_i < -\frac{1}{n^\beta\sqrt p}.$$
--
--   This elementary estimate is the source of the explicit lower bound in Lemma A.4.
--
--   **Formalization Note** The maximum and minimum are taken over the nonempty finite strategy set with `Finset.sup'` and `Finset.inf'`.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, Appendix, p. 33, Lemma A.5 (with the definition of U on the same page)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_Stability

namespace StochFictPlay.Potential

/-- Lemma A.5 (Hofbauer–Sandholm 2002, manuscript p. 33). If `θ` is a unit vector in the tangent
space `∏_α ℝ^{n^α}_0` of `Σ` (Euclidean norm), then some player `β` has
`max_i θ^β_i > 1/(n^β √p)` and `min_i θ^β_i < −1/(n^β √p)`. -/
theorem lemmaA5_exists_player (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (θ : Mixed n) (hθ : θ ∈ unitTangent n) :
    ∃ β : Fin p,
      1 / ((n β : ℝ) * Real.sqrt p) <
          Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn β⟩⟩) (θ β) ∧
        Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn β⟩⟩) (θ β) <
          -(1 / ((n β : ℝ) * Real.sqrt p)) := by sorry

end StochFictPlay.Potential
