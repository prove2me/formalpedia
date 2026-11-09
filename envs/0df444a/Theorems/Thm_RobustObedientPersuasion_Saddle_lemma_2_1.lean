-- Prove2me | Theorems.Thm_RobustObedientPersuasion_Saddle_lemma_2_1
-- name    : RobustObedientPersuasion.Saddle.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:01.086195+00:00
-- url     : https://prove2.me/theorems/41f2720d-2957-4b54-bdea-339649d001a7
-- title:
--   Lemma 2.1 — the identified set P(α) is nonempty, compact and polyhedral, with an FM representing system
-- statement:
--   Let $\Omega$ and $A$ be finite, $u:\Omega\times A\to\mathbb R$ the Receiver's utility, and $\alpha\in\Delta(A)$ an observed action distribution such that no action $a\in\operatorname{supp}(\alpha)$ is statewise strictly dominated under $u$, i.e. every obedience region $M_a$, $a\in\operatorname{supp}(\alpha)$, is nonempty. Then the data-driven identified set
--   $$\mathcal P(\alpha)=\sum_{a\in\operatorname{supp}(\alpha)}\alpha(a)M_a\subseteq\mathbb R^{|\Omega|}$$
--   is nonempty, compact and polyhedral: there is a finite linear system $\{\langle a_i,x\rangle\le b_i\}_{i=1}^n$ whose solution set is exactly $\mathcal P(\alpha)$. Consequently $\mathcal P(\alpha)$ satisfies the Farkas–Minkowski property: the characteristic cone of that representing system is closed.
--
--   This lemma supplies the geometry of the minimizing player's strategy set in the robust persuasion game: compactness and convexity are what the minimax argument of Theorem 3.1 needs, and the polytope structure is what places a worst-case prior at a vertex.
--
--   **Formalization Note** Polyhedrality and the FM property are asserted for one and the same finite system, as in the source proof (Appendix A).
--
--   Differences from the source:
--   - reading: "no action in supp(α) is statewise strictly dominated under u" → every M_a with α(a) > 0 is nonempty; reason: the paper states (p. 3) that this condition is equivalent to the existence of a posterior under which each supported action is optimal, and Appendix A uses exactly that meaning; this is domination by mixed actions (by the separating-hyperplane lemma, a is undominated by every mixed action iff M_a is nonempty), whereas the pure-action reading would make the lemma false (u(a,·) = (0.4, 0.4), u(a₁,·) = (1, 0), u(a₂,·) = (0, 1) — a is not dominated by a pure action yet M_a = ∅, so P(α) = ∅ when α(a) > 0)
--   - generalization: the model assumes a true prior μ₀ ∈ int Δ(Ω) rationalizing α → no μ₀ appears; reason: μ₀ does not enter P(α) or the conclusion, so the Lean statement covers every α of the source and specializes to it
--   - encoding: polyhedral set in ℝ^{|Ω|}, FM property via w*-closed characteristic cone → functions Ω → ℝ, a system indexed by Fin n, and closedness of the explicit unclosed conic hull in the product topology; reason: finite-dimensional identification; weak-star and Euclidean topologies coincide
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, Lemma 2.1, PDF p. 3; proof in Appendix A, PDF p. 8

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_FarkasMinkowski
import Definitions.Def_RobustObedientPersuasion_Saddle_Model

namespace RobustObedientPersuasion.Saddle

theorem lemma_2_1 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α) :
    (identifiedSet u α).Nonempty ∧ IsCompact (identifiedSet u α) ∧
      ∃ (n : ℕ) (a : Fin n → Ω → ℝ) (b : Fin n → ℝ),
        identifiedSet u α = systemSet a b ∧ HasFarkasMinkowski a b := by sorry

end RobustObedientPersuasion.Saddle
