-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_theorem_3_6
-- name    : ShapeMoment.LogConcave.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:04.363119+00:00
-- url     : https://prove2.me/theorems/a868143b-8ad1-4238-8a42-0f8757d7e195
-- title:
--   Theorem 3.6 — optimal extreme point and tight count
-- statement:
--   Consider (Rev-Cvx) in $\mathbb R^n$ with an $m\times n$ full-row-rank matrix $A$. Suppose the feasible set is nonempty and compact, the objective is continuous and quasiconcave, every $f_p$ is differentiable, and $\{x\ge0:f_p(x)>0\}$ is convex for each $p$. An optimal extreme point exists, and every optimal extreme point $x^*$ satisfies
--
--   $$n-m\le\#\{p:f_p(x^*)=0\}+\#\{j:x^*_j=0\}.$$
--
--   The count is the first two paragraphs of Theorem 3.6. **Formalization Note** Reverse convexity is relative to the nonnegative orthant, as used in the proof on page 26.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 10, Theorem 3.6, first two paragraphs; Assumption 1

import Definitions.Def_ShapeMoment_LogConcave_ReverseConvex

namespace ShapeMoment.LogConcave

theorem theorem_3_6 (n m P : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : (Fin n → ℝ) → ℝ)
    (f : Fin P → (Fin n → ℝ) → ℝ)
    (hc : Continuous c) (hqc : QuasiconcaveOn ℝ Set.univ c)
    (hrank : A.rank = m) (hfdiff : ∀ p, Differentiable ℝ (f p))
    (hrc : ∀ p, Convex ℝ {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧ 0 < f p x})
    (hne : (revCvxFeasible A b f).Nonempty)
    (hcompact : IsCompact (revCvxFeasible A b f)) :
    (∃ x ∈ (revCvxFeasible A b f).extremePoints ℝ,
      IsMinOn c (revCvxFeasible A b f) x) ∧
    ∀ x ∈ (revCvxFeasible A b f).extremePoints ℝ,
      IsMinOn c (revCvxFeasible A b f) x →
      n - m ≤ (Finset.univ.filter (fun p : Fin P => f p x = 0)).card +
        (Finset.univ.filter (fun j : Fin n => x j = 0)).card := by sorry

end ShapeMoment.LogConcave
