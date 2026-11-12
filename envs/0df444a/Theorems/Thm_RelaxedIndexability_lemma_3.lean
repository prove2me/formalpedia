-- Prove2me | Theorems.Thm_RelaxedIndexability_lemma_3
-- name    : RelaxedIndexability.lemma_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:21:08.04337+00:00
-- url     : https://prove2.me/theorems/0186acfc-d53a-4dc0-a3e5-018623ac7310
-- title:
--   Lemma 3 — the linear equation set (35)–(36) determines $\hat V_{\beta,m}(p_0), \dots, \hat V_{\beta,m}(p_{K-1})$ (corrected: (36) as in `renewal_equations`)
-- statement:
--   Let an arm have a row-stochastic transition matrix $\mathbf P$ with rows $p_0, \dots, p_{K-1}$ and rewards $B$, let $0<\beta<1$, let the belief $\omega$ be fixed as a point in the threshold, and let $m$ be a subsidy. Consider the linear equation set (35)–(36) in the $2K$ unknowns $x_k$ (for $\hat V_{\beta,m}(p_k)$) and $y_k$ (for $\hat V_{\beta,m}(\mathcal T^{L(p_k,\omega)}(p_k); u=1)$), with its coefficients determined by the first-crossing times $L(\cdot, \omega)$, $m$, $\beta$, $\mathbf P$ and $B$. Then:
--
--   1. the system has a solution;
--   2. every solution has $x_k = \hat V_{\beta,m}(p_k)$ for all $k$: the $\hat V(p_k)$-part of the solution is unique and equals the values of the threshold policy;
--   3. the matrix $I_K - \beta G(\mathbf P)$ is invertible, where the $k$-th row of $G(\mathbf P)$ is $g(p_k) = \beta^{L(p_k,\omega)} p_k \mathbf P^{L(p_k,\omega)}$.
--
--   Together with the indifference equation (37), this linear system is what makes the approximated Whittle index computable in closed form.
--
--   Differences from the source:
--   - correction: the system (35)–(36) as printed, with T^{L(p_k,ω)}(ω) in (36) → the system with T^{L(p_k,ω)}(p_k) in (36); reason: the printed (36) is false for the threshold policy's values (counterexample in `renewal_equations`: K = 2, P = [[1/2,1/2],[1/5,4/5]], B = (0,1), β = 1/2, ω = (1,0)); the paper's own proof (EC.38) solves the corrected system.
--   - reading: "has a unique solution consisting of the value functions {V̂(p_k)}" in 2K unknowns → a solution exists and every solution has x = (V̂(p_k))_k; reason: when L(p_k,ω) = +∞ the unknown V̂(T^{L}(p_k); u=1) is multiplied by β^{+∞} = 0 and is not determined, so uniqueness is that of the V̂(p_k)-part, as the lemma says.
--   - reading: equations with L(p_k,ω) = +∞ → x_k = m/(1−β), with no (36) for that k; reason: β^{+∞} = 0, and T^{+∞}(p_k) is not a belief.
--   - generalization: the lemma's conclusion → adds the invertibility of I_K − βG(P); reason: the proof (EC.5, p.ec9) establishes it, and dropping the clause gives the printed lemma.
--   - generalization: the standing assumptions P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: not used; the statement for every row-stochastic P and every B contains the source's case.
--   - encoding: V̂ is the expected total discounted reward of π_{β,m} → the limit of the n-horizon expected discounted rewards computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Lemma 3, p.21; proof EC.5, p.ec9

import Mathlib
import Definitions.Def_RelaxedIndexability_thresholdValue
import Definitions.Def_RelaxedIndexability_RenewalSystem
import Definitions.Def_RelaxedIndexability_approxWhittle

open Matrix

namespace RelaxedIndexability

/-- **Lemma 3** (Liu, arXiv:2107.11939v4, Lemma 3, p.21; proof EC.5, p.ec9). With `ω` fixed as a
point in the threshold, the linear equation set (35)–(36) (with (36) corrected) has a solution, and
every solution has the same `V̂(p_k)`-component, namely the threshold policy's values
`(V̂_{β,m}(p₀), …, V̂_{β,m}(p_{K−1}))`. Moreover `I_K − βG(P)` is invertible.

**Formalization Note.** The unknowns `y k` standing for `V̂(T^{L}(p_k); u = 1)` are not determined
when `L(p_k, ω) = +∞`; the lemma's uniqueness is that of the `V̂(p_k)`-component. -/
theorem lemma_3 {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) (m : ℝ) :
    (∃ x y : Fin K → ℝ, RenewalSystem β P B ω m x y) ∧
    (∀ x y : Fin K → ℝ, RenewalSystem β P B ω m x y →
      x = fun k => thresholdValue β P B ω m (P k)) ∧
    IsUnit (1 - β • GMat β P B ω) := by sorry

end RelaxedIndexability
