-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_lemma_3_1
-- name    : SubmodMFG.Supplement.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:23:28.230436+00:00
-- url     : https://prove2.me/theorems/28a9fc53-fafe-4e3f-89a9-e89c8fa37e4e
-- title:
--   Lemma 3.1 (corrected: weak convergence read through survival functions) — bounded monotone sequences in $\mathcal M_{\le1}$ converge weakly to their supremum or infimum
-- statement:
--   Let $\mathcal M_{\le1}$ be the sub-probability measures on $\mathbb R$, ordered by first-order stochastic dominance $\le_{st}$ (comparison of survival functions $\mu_0(s)=\mu((s,\infty))$).
--
--   1. If $(\mu^n)_{n\in\mathbb N}\subset\mathcal M_{\le1}$ is bounded above and below and nondecreasing, then its supremum $\sup_n\mu^n$ with respect to $\le_{st}$ exists and $\mu^n\to\sup_n\mu^n$ weakly.
--   2. If $(\mu^n)$ is bounded above and below and nonincreasing, then its infimum $\inf_n\mu^n$ exists and $\mu^n\to\inf_n\mu^n$ weakly.
--
--   Here $\mu^n\to\mu$ weakly means
--   $$\mu^n_0(s)\longrightarrow\mu_0(s)\qquad\text{for every continuity point }s\text{ of }\mu_0 .$$
--
--   The lemma identifies order limits of monotone sequences with weak limits; it is used in Theorem 3.3 and in the convergence statements of §§5–7.
--
--   **Formalization Note** Supremum and infimum are least upper and greatest lower bounds of the range for $\le_{st}$; the conclusion holds for every such bound.
--
--   Differences from the source:
--   - correction: weak convergence of sub-probability measures (narrow convergence against bounded continuous functions) → WeakConv: pointwise convergence of survival functions at continuity points of the limit (the characterization stated on p.9); reason: with narrow convergence the nonincreasing case is false: δ_{−n} is nonincreasing and bounded for ≤st (0 ≤st δ_{−n} ≤st δ_0), its infimum is the zero measure, and ∫1 dδ_{−n} = 1 does not tend to 0; the paper's proof uses exactly the survival-function convergence (DISPROOF.md)
--   - encoding: bounded sequence; its supremum/infimum w.r.t. ≤st → BddAbove and BddBelow of the range for the preorder ≤st on {µ : Measure ℝ // µ univ ≤ 1}; the conclusion asserts that a least upper (greatest lower) bound exists and that the sequence converges to it; reason: ≤st is antisymmetric on finite Borel measures, so the bound is unique
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §3, Lemma 3.1, p.9

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb

namespace SubmodMFG.Supplement

/-- **Lemma 3.1** — bounded monotone sequences of sub-probability measures converge weakly to
their supremum (infimum) for `≤st`.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §3, Lemma 3.1, p.9: "Every bounded and nondecreasing or nonincreasing
sequence (µⁿ)ₙ∈ℕ ⊂ M≤1 converges weakly to its supremum or infimum w.r.t. ≤st, respectively."

**Formalization Note.** "Bounded" is bounded above and below for `≤st`. Each clause asserts that
the supremum (infimum) of the range exists and that the sequence converges weakly, in the sense
of `WeakConv` (pointwise convergence of survival functions at continuity points of the limit,
the characterization of p.9), to it. -/
theorem lemma_3_1 :
    (∀ μ : ℕ → SubProb, BddAbove (Set.range μ) → BddBelow (Set.range μ) → Monotone μ →
      (∃ b, IsLUB (Set.range μ) b) ∧ ∀ b, IsLUB (Set.range μ) b → WeakConv μ b) ∧
    (∀ μ : ℕ → SubProb, BddAbove (Set.range μ) → BddBelow (Set.range μ) → Antitone μ →
      (∃ b, IsGLB (Set.range μ) b) ∧ ∀ b, IsGLB (Set.range μ) b → WeakConv μ b) := by sorry

end SubmodMFG.Supplement
