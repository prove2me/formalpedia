-- Prove2me | Theorems.Thm_PolyVoting_proposition_1
-- name    : PolyVoting.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:09.44896+00:00
-- url     : https://prove2.me/theorems/21c81747-c4e9-4a5b-a799-f6a09056441c
-- title:
--   Proposition 1 — the stake process is a Pólya urn run on an independent geometric clock
-- statement:
--   Let $0=T_0<T_1<\cdots$ be arrival times whose inter-arrival times $T_{j+1}-T_j$, $j\ge0$, are independent, each geometric on $\{1,2,\dots\}$ with success probability $(N+j)^{-\alpha}$, and let $L_t=\#\{j\ge1:T_j\le t\}$ be the associated counting process. Let $(\boldsymbol u_j)_{j\ge0}$ be a Pólya urn with $K$ colours and initial composition $\boldsymbol n_0$, independent of $(T_j)$. Then the process $\boldsymbol l_t=\boldsymbol u_{L_t}$, which equals $\boldsymbol u_j$ on $T_j\le t<T_{j+1}$, has the law of the stake process:
--   $$(\boldsymbol n_t,\ t\ge0)\overset{d}{=}(\boldsymbol u_{L_t},\ t\ge0).$$
--
--   This is the structural fact of the model: the Poly($\alpha$) rule changes when stakes are awarded, and not to whom.
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
--   - encoding: the Pólya urn with K colours and initial composition n_{k,0} → a `Model` with α = 0 and the same n₀, the Poly(0) instance of the same structure; reason: p.5 identifies α = 0 with the Pólya urn, and at α = 0 the step law is "colour k is drawn with probability n_{k,t}/N_t and one ball of colour k is added"
--   - reading: "a copy of the Pólya urn process" → the urn U is independent of the arrival times (hT_urn); reason: the proof composes the two laws and the statement is false for a dependent copy
--   - reading: "K colors and N initial balls" → the urn starts from the composition n₀; reason: the two processes agree at t = 0 only then
--   - encoding: geometric distribution with parameter p on inter-arrival times → the first-success law: P(T_{j+1} − T_j = s + 1) = (1 − p)^s p with p = (N + j)^{−α}; reason: 0 = T_0 < T_1 < ⋯ forces values in {1, 2, …}; the point masses determine the law
--   - encoding: (l_t) defined piecewise on [T_k, T_{k+1}) → U evaluated at #{j ∈ [1, t] : T_j ≤ t}; reason: the count is L_t, and T_j ≥ j makes the range [1, t] sufficient
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, Proposition 1, pp.5–6

import Mathlib
import Definitions.Def_PolyVoting_Model

open MeasureTheory ProbabilityTheory

namespace PolyVoting

/-- **Proposition 1** (Tang & Yao, *Polynomial Voting Rules*, arXiv:2206.10105v5, pp.5–6): the stake
process is a Pólya urn run on an independent clock with geometric holding times.

**Formalization Note.** `T` holds the arrival times `0 = T 0 < T 1 < ⋯`, the increment
`T (j + 1) - T j` has the geometric law with success probability `(N + j) ^ (-α)` on `{1, 2, …}`
(first-success convention), and `U` is the urn, the `α = 0` model with the same `n₀`. The count
`#{j ∈ [1, t] : T j ≤ t}` is the counting process `L_t`, so the process `l` of the paper is
`l_t = U (L_t)`. "Copy of the Pólya urn" is read as independent of the arrival times. The equality
is of laws on the path space `ℕ → (Fin K → ℕ)` with the product σ-algebra. -/
theorem proposition_1 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {K : ℕ} {α : ℝ} {n₀ : Fin K → ℕ}
    (M : Model μ K α n₀) (U : Model μ' K 0 n₀)
    (T : ℕ → Ω' → ℕ) (hT_meas : ∀ j, Measurable (T j))
    (hT_zero : ∀ ω, T 0 ω = 0) (hT_lt : ∀ j ω, T j ω < T (j + 1) ω)
    (hT_indep : iIndepFun (fun j ω => T (j + 1) ω - T j ω) μ')
    (hT_law : ∀ j s : ℕ, μ' {ω | T (j + 1) ω - T j ω = s + 1} =
      ENNReal.ofReal ((1 - (((∑ k, n₀ k : ℕ) : ℝ) + j) ^ (-α)) ^ s *
        (((∑ k, n₀ k : ℕ) : ℝ) + j) ^ (-α)))
    (hT_urn : IndepFun (fun ω j => T j ω) (fun ω t => U.n t ω) μ') :
    μ.map (fun ω t => M.n t ω) =
      μ'.map (fun ω t => U.n ((Finset.Icc 1 t).filter fun j => T j ω ≤ t).card ω) := by sorry

end PolyVoting
