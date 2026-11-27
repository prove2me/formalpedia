-- Prove2me | Theorems.Thm_RelaxedIndexability_Supplement_lemma_1
-- name    : RelaxedIndexability.Supplement.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:03:29.061252+00:00
-- url     : https://prove2.me/theorems/31bfface-c28c-4517-9aad-98da3ac24816
-- title:
--   Lemma 1 — the optimal value $V_{\beta,m}(\omega)$ is convex and Lipschitz in $\omega$ and in $m$
-- statement:
--   Consider one arm with $K$ states, a row-stochastic transition matrix $\mathbf P$ and a reward vector $B$, a discount factor $\beta\in(0,1)$, and let $V_{\beta,m}(\omega)$ be the optimal value of the single-armed bandit with subsidy $m$ from belief $\omega$. Then:
--
--   1. for every $m$, $\omega\mapsto V_{\beta,m}(\omega)$ is convex on the belief simplex;
--   2. there is a constant $C$ such that for every $m$, $\omega\mapsto V_{\beta,m}(\omega)$ is $C$-Lipschitz on the belief simplex;
--   3. for every belief $\omega$, $m\mapsto V_{\beta,m}(\omega)$ is convex on $\mathbb R$;
--   4. there is a constant $C'$ such that for every belief $\omega$, $m\mapsto V_{\beta,m}(\omega)$ is $C'$-Lipschitz on $\mathbb R$.
--
--   Convexity in $m$ gives the one-sided derivatives used in Theorem 1, and continuity in $\omega$ underlies the threshold structure of the optimal policy (Lemma 2).
--
--   **Formalization Note** Convexity holds separately in each variable, as proved in EC.1; joint convexity in $(\omega,m)$ is not claimed and fails in general. The constants may depend on $\beta$, $\mathbf P$ and $B$; the proof gives $B_{K-1}/(1-\beta)$ and $1/(1-\beta)$. Beliefs carry the maximum norm, which is equivalent to the paper's $\ell^1$ norm.
--
--   Differences from the source:
--   - reading: Lipschitz continuous in both ω and m → a Lipschitz constant in ω uniform in m, and a Lipschitz constant in m uniform in ω; reason: the stronger of the two readings, and the one EC.1 proves (constants B_{K−1}/(1−β) and 1/(1−β), p.ec3–ec4)
--   - generalization: P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: the lemma does not use them; every row-stochastic P and every B include the source's case
--   - generalization: an arm has a positive finite number K of states → K is any natural number, including 0; reason: the K = 0 simplex is empty and every clause is vacuous, while every source arm has K > 0
--   - encoding: ℓ¹ norm on beliefs → the maximum norm of Fin K → ℝ; reason: equivalent norms on a finite-dimensional space, so Lipschitz continuity is the same property
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Lemma 1, p.13; proof EC.1, pp.ec1–ec4

import Mathlib
import Definitions.Def_RelaxedIndexability_Supplement_optimalValue

open Matrix
open scoped NNReal

namespace RelaxedIndexability.Supplement

/-- **Lemma 1** (Liu, arXiv:2107.11939v4, Lemma 1, p.13; proof EC.1, pp.ec1–ec4). The optimal value
`V_{β,m}(ω)` of the single-armed bandit with subsidy is

1. for every `m`, convex in `ω` on the belief simplex;
2. Lipschitz continuous in `ω` on the simplex, with a constant independent of `m`;
3. for every `ω` in the simplex, convex in `m`;
4. Lipschitz continuous in `m`, with a constant independent of `ω`.

**Formalization Note.** Convexity is separate in the two variables, as proved in EC.1; joint
convexity is not claimed. The constants may depend on `β`, `P` and `B`. The norm on beliefs is the
maximum norm of `Fin K → ℝ` (the paper uses the equivalent ℓ¹ norm). -/
theorem lemma_1 {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ) :
    (∀ m : ℝ, ConvexOn ℝ (stdSimplex ℝ (Fin K)) (fun ω => optimalValue β P B m ω)) ∧
    (∃ C : ℝ≥0, ∀ m : ℝ,
      LipschitzOnWith C (fun ω => optimalValue β P B m ω) (stdSimplex ℝ (Fin K))) ∧
    (∀ ω ∈ stdSimplex ℝ (Fin K), ConvexOn ℝ Set.univ (fun m => optimalValue β P B m ω)) ∧
    (∃ C : ℝ≥0, ∀ ω ∈ stdSimplex ℝ (Fin K),
      LipschitzWith C (fun m => optimalValue β P B m ω)) := by sorry

end RelaxedIndexability.Supplement
