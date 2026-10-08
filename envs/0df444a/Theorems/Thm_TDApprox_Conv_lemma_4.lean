-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_4
-- name    : TDApprox.Conv.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:44.260294+00:00
-- url     : https://prove2.me/theorems/808f9569-2a4b-4037-b373-8a8174c44655
-- title:
--   Lemma 4, p. 14 — ‖T^(λ)J − T^(λ)J̄‖_D ≤ (α(1−λ)/(1−αλ))‖J − J̄‖_D ≤ α‖J − J̄‖_D
-- statement:
--   Under Assumption 1, let $\alpha \in (0,1)$ and $\lambda \in [0,1]$. For any $J, \bar J \in L_2(S,D)$,
--   $$\|T^{(\lambda)}J - T^{(\lambda)}\bar J\|_D \le \frac{\alpha(1-\lambda)}{1-\alpha\lambda}\|J - \bar J\|_D \le \alpha\|J - \bar J\|_D.$$
--
--   So $T^{(\lambda)}$ is a contraction of $L_2(S,D)$ with modulus $\alpha(1-\lambda)/(1-\alpha\lambda)$. At $\lambda = 1$ the modulus is $0$, since $T^{(1)}$ is the constant map $J \mapsto J^*$.
--
--   **Formalization Note.** The page says "Under Assumption 1(a)". The statement here assumes all of Assumption 1, because $T^{(\lambda)}J$ is only shown to be defined on $L_2(S,D)$ under Assumption 1 (Lemma 3, which the proof uses) and $T^{(1)}J = J^*$ needs Assumption 1(b)–(c). Both inequalities of the chain are stated.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 4, p. 14

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 4** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 14). For any `J, J̄ ∈ L₂(S, D)` and
`λ ∈ [0, 1]`,
`‖T^(λ)J − T^(λ)J̄‖_D ≤ (α(1 − λ)/(1 − αλ)) ‖J − J̄‖_D ≤ α ‖J − J̄‖_D`.
The page says "Under Assumption 1(a)"; the hypothesis here is all of Assumption 1, under which
`T^(λ)` is defined on `L₂(S, D)` (Lemma 3) and `T^(1)J = J*`. -/
theorem lemma_4 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1 : Assumption1 P π g α) (J Jb : S → ℝ) (hJ : MemL2D π J) (hJb : MemL2D π Jb)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    normD π (Tlam P g α lam J - Tlam P g α lam Jb) ≤
        α * (1 - lam) / (1 - α * lam) * normD π (J - Jb) ∧
      α * (1 - lam) / (1 - α * lam) * normD π (J - Jb) ≤ α * normD π (J - Jb) := by sorry

end TDApprox.Conv
