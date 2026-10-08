-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_5
-- name    : TDApprox.Conv.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:50.399952+00:00
-- url     : https://prove2.me/theorems/e93f8100-fe21-42d4-ab2e-9bd30d48c4f4
-- title:
--   Lemma 5, p. 14 — ΠT^(λ) is a contraction with a unique fixed point Φ′r*, and ‖Φ′r* − J*‖_D ≤ ‖ΠJ* − J*‖_D/(1 − α(1−λ)/(1−αλ))
-- statement:
--   Under Assumptions 1 and 2 (unique invariant distribution $\pi > 0$, square-integrable costs, finite $J^*$; linearly independent basis functions $\phi_k$ with $E_0[\phi_k^2] < \infty$), let $\alpha \in (0,1)$, $\lambda \in [0,1]$, and let $\Pi = \Phi'(\Phi D\Phi')^{-1}\Phi D$ be the projection of Eq. (1). Then:
--   1. $\Pi T^{(\lambda)}$ maps $L_2(S,D)$ into itself;
--   2. it is a contraction of $\|\cdot\|_D$: there is $c \in [0,1)$ with $\|\Pi T^{(\lambda)}J - \Pi T^{(\lambda)}\bar J\|_D \le c\|J - \bar J\|_D$ for all $J,\bar J \in L_2(S,D)$;
--   3. it has a unique fixed point in $L_2(S,D)$, of the form $\Phi'r^*$ for a unique $r^* \in \mathbb R^K$;
--   4. this $r^*$ satisfies
--   $$\|\Phi' r^* - J^*\|_D \le \frac{\|\Pi J^* - J^*\|_D}{1 - \alpha(1-\lambda)/(1-\alpha\lambda)}.$$
--
--   The fixed point $\Phi'r^*$ is the limit that TD($\lambda$) is shown to reach, and the bound compares its error with the best approximation error $\|\Pi J^* - J^*\|_D$ available in the span of the basis functions.
--
--   **Formalization Note.** Fixed points are equalities of functions on $S$; since $\pi(i) > 0$ for all $i$ this is the same as equality in $L_2(S,D)$. "Unique choice of $r^*$" is stated as: every $r$ with $\Pi T^{(\lambda)}(\Phi'r) = \Phi'r$ equals $r^*$.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 5, p. 14

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 5** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 14). Under Assumptions 1 and 2, for
`λ ∈ [0, 1]`, `ΠT^(λ)(·)` maps `L₂(S, D)` into itself and is a contraction of `‖·‖_D`; it has a
unique fixed point in `L₂(S, D)`, which is of the form `Φ′r*` for a unique choice of `r*`; and
`‖Φ′r* − J*‖_D ≤ ‖ΠJ* − J*‖_D / (1 − α(1 − λ)/(1 − αλ))`. -/
theorem lemma_5 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (∀ J, MemL2D π J → MemL2D π (proj π φ (Tlam P g α lam J))) ∧
    (∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ J Jb, MemL2D π J → MemL2D π Jb →
      normD π (proj π φ (Tlam P g α lam J) - proj π φ (Tlam P g α lam Jb)) ≤
        c * normD π (J - Jb)) ∧
    ∃ rstar : Fin K → ℝ,
      proj π φ (Tlam P g α lam (Jtilde φ rstar)) = Jtilde φ rstar ∧
      (∀ J, MemL2D π J → proj π φ (Tlam P g α lam J) = J → J = Jtilde φ rstar) ∧
      (∀ r, proj π φ (Tlam P g α lam (Jtilde φ r)) = Jtilde φ r → r = rstar) ∧
      normD π (Jtilde φ rstar - Jstar P g α) ≤
        normD π (proj π φ (Jstar P g α) - Jstar P g α) / (1 - α * (1 - lam) / (1 - α * lam)) := by sorry

end TDApprox.Conv
