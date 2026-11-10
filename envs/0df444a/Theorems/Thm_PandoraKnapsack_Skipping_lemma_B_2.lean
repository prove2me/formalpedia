-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_lemma_B_2
-- name    : PandoraKnapsack.Skipping.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:25:41.338122+00:00
-- url     : https://prove2.me/theorems/031301e2-59cd-4c9c-bcba-7ecea115b1bd
-- title:
--   Lemma B.2 — the uniform lift of a compact optimum is feasible and quarter-optimal
-- statement:
--   Let $I$ be a valid MPK instance with capacity $T$, let $b\in\mathbb N$ and let $x^*$ be an optimal solution of $\Psi_P(b)$. Let $y$ be the real array on $[n]\times[m]\times\{0,\dots,b\}$ given by $y_{i,j,0}=x^*_{i,j,0}$ and $y_{i,j,t}=x^*_{i,j,\tau}/|I_\tau|$ for $\tau\in T_b\setminus\{0\}$ and $t\in I_\tau=[\tau,2\tau)\cap\{0,\dots,b\}$. Then $y$ is a feasible solution of $\Psi(b)$, and its value is at least a quarter of the optimal value of $\Psi(b)$: for every feasible $x$ of $\Psi(b)$,
--   $$\tfrac14\sum_{i,j}\sum_{t\le b}w_{i,j,t}x_{i,j,t}\ \le\ \sum_{i,j}\sum_{t\le b}w_{i,j,t}\,y_{i,j,t}.$$
--
--   Differences from the source:
--   - reading: let y ∈ [n] × [m] × {0, …, b} be defined by y_{i,j,0} = x*_{i,j,0} and y_{i,j,t} = x*_{i,j,τ}/|I_τ| → y = liftY b x*, a real array indexed by [n] × [m] × {0, …, b}; reason: obvious typing typo (insight I2): the coordinate formulas and the proof define an array, not a triple of indices
--   - encoding: at least a quarter of the optimal LP value → objective(y) ≥ objective(x)/4 for every feasible x of Ψ(b); reason: the optimum of Ψ(b) is attained, so this is the same inequality; no real supremum is taken
--   - encoding: the optimal solution x* of Ψ_P(b) → any optimal solution x* of Ψ_P(b); reason: the source does not assume uniqueness; its argument uses only optimality
--   - generalization: b with T_b = {0} ∪ {2^l : l ≤ ⌊log b⌋}, undefined at b = 0 → every b ∈ ℕ, with T_0 = {0}; reason: for b ≥ 1 the breakpoint set is the source's; at b = 0 the lift is x* itself and Ψ_P(0) = Ψ(0)
--   - encoding: y defined on t ∈ {0, …, b} → liftY sets coordinates t > b to 0; arrays are indexed by ℕ; reason: coordinates outside the index set enter neither the constraints nor the objective
--   - encoding: items [n] and choices [m] indexed from 1 → Fin n and Fin m, indexed from 0; reason: index shift; same instances
--   - reading: item-choice costs p_i^j paid up front (sign not stated) → 0 ≤ p_i^j in IsValid; reason: §2 calls p_i^j a cost incurred up front and Definition 2.1 divides by it; a negative cost would reward overflow, which the model never does
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Lemma B.2, printed p. 41 (PDF 43)

import Definitions.Def_PandoraKnapsack_Skipping_CompactLP

namespace PandoraKnapsack.Skipping

/-- **Lemma B.2** (Barak et al. 2026, *Pandora's Knapsack via Simple Policies*, supplied PDF,
SHA256 45e5830b…7a2d, printed p. 41, PDF 43). Let `x*` be the optimal solution of `Ψ_P(b)` and
let `y` be defined by `y_{i,j,0} = x*_{i,j,0}` and `y_{i,j,t} = x*_{i,j,τ} / |I_τ|` for
`τ ∈ T_b ∖ {0}` and `t ∈ I_τ`. Then `y` is a feasible solution of `Ψ(b)` yielding a value of at
least a quarter of the optimal LP value.

**Formalization Note.** `y` is the real array `liftY b x*` on `[n] × [m] × {0, …, b}` (the source
writes `y ∈ [n] × [m] × {0, …, b}`). "At least a quarter of the optimal value of `Ψ(b)`" is
stated against every feasible solution of `Ψ(b)`. -/
theorem lemma_B_2 {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (b : ℕ)
    (xStar : LPArray n m) (hx : PsiPOptimal I b xStar) :
    PsiFeasible I b (liftY b xStar) ∧
      ∀ x : LPArray n m, PsiFeasible I b x →
        psiObjective I b x / 4 ≤ psiObjective I b (liftY b xStar) := by sorry

end PandoraKnapsack.Skipping
