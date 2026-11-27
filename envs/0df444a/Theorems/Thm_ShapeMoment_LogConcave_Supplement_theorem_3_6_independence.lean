-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_Supplement_theorem_3_6_independence
-- name    : ShapeMoment.LogConcave.Supplement.theorem_3_6_independence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:08:55.755625+00:00
-- url     : https://prove2.me/theorems/e65252f1-4812-438e-934c-02a1e04397c5
-- title:
--   Theorem 3.6, final paragraph, p. 10 — n − m linearly independent active gradients and unit vectors (first two paragraphs: ShapeMoment.LogConcave.theorem_3_6)
-- statement:
--   Consider the reverse convex program (Rev-Cvx)
--   $$\min\ c(x)\quad\text{s.t.}\quad Ax=b,\ \ f_p(x)\le 0\ (p\in[1,P]),\ \ x\ge 0,$$
--   with $c,f_p:\mathbb R^n\to\mathbb R$, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, where each set $\{x\ge0: f_p(x)>0\}$ is convex (reverse convexity with respect to $\mathbb R^n_+$). Assume Assumption 1: $c$ is continuous and quasiconcave, $A$ has full row rank, every $f_p$ is differentiable, and the feasible region $X$ is nonempty and compact.
--
--   Let $x^*$ be an optimal extreme point of $X$ and $S=S(x^*)=\{j: x^*_j>0\}$. If every tight constraint, $f_p(x^*)=0$, satisfies $[\nabla f_p(x^*)]_S\notin\mathcal L(S)$, the span of the rows of $A_S$, then some $n-m$ of the vectors
--   $$\{\nabla f_p(x^*): f_p(x^*)=0\}\cup\{e_j: x^*_j=0\}$$
--   are linearly independent.
--
--   This is the "in addition" part of Theorem 3.6; the existence of an optimal extreme point and the count of $n-m$ tight constraints are the published theorem `ShapeMoment.LogConcave.theorem_3_6`. The independence clause is what the proof of Theorem 4.2 needs, because (DMP-IFR′) has about $2n$ inequality constraints and a bare count of tight ones does not determine the solution.
--
--   **Formalization Note** "$n-m$ of the vectors are linearly independent" is stated as the existence of a finite set of exactly $n-m$ distinct vectors from the family that is linearly independent. Full row rank gives $m\le n$, so $n-m$ is not truncated.
--
--   Differences from the source:
--
--   - encoding: Theorem 3.6 has three conclusions → this item states the third; reason: the first two are the published theorem ShapeMoment.LogConcave.theorem_3_6 (a868143b-8ad1-4238-8a42-0f8757d7e195) with the same hypotheses, and the two items together state the whole theorem
--   - reading: "the set {x : f_p(x) ≤ 0} is reverse convex w.r.t. the nonnegative orthant" → {x ≥ 0 : f_p(x) > 0} is convex; reason: the same reading as the published first two paragraphs and as Subclaim 1 (p. 26)
--   - encoding: ∇f_p(x) → the vector of directional derivatives Df_p(x)(e_j); reason: equal to the gradient for a differentiable function
--   - reading: "n − m of the vectors … are linearly independent" → a set of n − m distinct vectors of the family is linearly independent; reason: the plain meaning; an independent set has no repeated vector
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 10, Theorem 3.6 (third paragraph), Assumption 1, (Rev-Cvx); notation for S(x), A_S, L(S) on p. 10

import Definitions.Def_ShapeMoment_LogConcave_ReverseConvex
import Definitions.Def_ShapeMoment_LogConcave_Supplement_ActiveGradients

namespace ShapeMoment.LogConcave.Supplement

theorem theorem_3_6_independence (n m P : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : (Fin n → ℝ) → ℝ)
    (f : Fin P → (Fin n → ℝ) → ℝ)
    (hc : Continuous c) (hqc : QuasiconcaveOn ℝ Set.univ c)
    (hrank : A.rank = m) (hfdiff : ∀ p, Differentiable ℝ (f p))
    (hrc : ∀ p, Convex ℝ {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧ 0 < f p x})
    (hne : (revCvxFeasible A b f).Nonempty)
    (hcompact : IsCompact (revCvxFeasible A b f)) :
    ∀ x ∈ (revCvxFeasible A b f).extremePoints ℝ,
      IsMinOn c (revCvxFeasible A b f) x →
      (∀ p, f p x = 0 →
        restrictTo (supportSet x) (grad (f p) x) ∉ rowSpanOn A (supportSet x)) →
      ∃ s : Finset (Fin n → ℝ), (↑s : Set (Fin n → ℝ)) ⊆ activeVectors f x ∧
        s.card = n - m ∧
        LinearIndependent ℝ (fun v : (↑s : Set (Fin n → ℝ)) => (v : Fin n → ℝ)) := by sorry

end ShapeMoment.LogConcave.Supplement
