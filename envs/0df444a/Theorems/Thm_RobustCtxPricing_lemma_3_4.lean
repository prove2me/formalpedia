-- Prove2me | Theorems.Thm_RobustCtxPricing_lemma_3_4
-- name    : RobustCtxPricing.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:08.461643+00:00
-- url     : https://prove2.me/theorems/790b297d-1ef3-449e-9c09-90c71069be66
-- title:
--   Lemma 3.4 — the commit price lies in $[v_t-\frac1{4T},\,v_t]$
-- statement:
--   Let $d\ge1$ and $\theta^\star\in\Theta$. Let $\mathcal H_1,\dots,\mathcal H_{2\bar C+1}$ be evidence sets of which at most $\bar C$ are not correct, let $u$ be a context, and for each $j$ let $\lambda^j$ satisfy (1) for $\mathcal H_j$ and $u$. Let $\underline v$ be the commit price of Algorithm 2: the $(\bar C+1)$-st largest of the lower endpoints $\hat v_j(u)-\frac1{8T}$, $\hat v_j(u)=\sum_i\lambda^j_ip^j_i$. Then, with $v=\langle\theta^\star,u\rangle$,
--   $$
--   \underline v\in\Big[v-\frac1{4T},\ v\Big].
--   $$
--   Hence a committed price always sells, and a commit round costs at most $\frac1{4T}$ in regret.
--
--   Differences from the source:
--   - generalization: ϵ = T⁻³ and the context u_t ∈ 𝓑_d(0,1) of the algorithm → any real ϵ, any T, C̄ ∈ ℕ and any context u ∈ ℝ^d; reason: the statement holds for all of them and specializes to the algorithm's values
--   - generalization: the solutions of (1) used by Commit → any coefficients λ^j achieving (1); reason: specializes to the minimizers
--   - encoding: "at most C̄ evidence sets are not correct", "(C̄ + 1)-st largest lower endpoint" → at most C̄ indices j ∈ Fin (2C̄+1) with 𝓗_j not correct; the entry with index C̄ of the lower endpoints sorted non-increasingly; reason: Lean convention; same instances
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - encoding: the dimension d ∈ ℕ of ℝ^d → a natural number d with 1 ≤ d; reason: the context dimension of the model; d = 0 has no directions and is not an instance of it
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Lemma 3.4, p.15 (with Algorithm 2, p.13, and Equation (2), p.14)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence

namespace RobustCtxPricing

/-- **Lemma 3.4.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §3.2.1, p.15: "Suppose that at most `C̄` evidence sets are not correct
and every evidence set satisfies Equation (1) for a context `u_t`. Then, the price posted by the
Commit procedure satisfies: `p_t ∈ [v_t − 1/(4T), v_t]`."

For `θ⋆ ∈ Θ`, `2C̄ + 1` evidence sets `H_j` of which at most `C̄` are not correct, a context `u`
and coefficients `λ^j` satisfying (1) for every `j`, the Commit price (the `(C̄ + 1)`-st largest
lower endpoint `v̂_j(u) − 1/(8T)`, Algorithm 2) lies in `[v − 1/(4T), v]`, `v = ⟨θ⋆, u⟩`.

**Formalization Note.** Stated for every `ϵ`, `T` and `C̄` (Algorithms 1 and 4 use `ϵ = T⁻³` and
their own `C̄`), and for every choice of coefficients `λ^j` satisfying (1). -/
theorem lemma_3_4 (d : ℕ) (hd : 1 ≤ d) (ϵ : ℝ) (T Cb : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (hθ : θ ∈ Theta d) (H : Fin (2 * Cb + 1) → List (EuclideanSpace ℝ (Fin d) × ℝ))
    (hcorr : {j | ¬ SetCorrect ϵ θ (H j)}.ncard ≤ Cb)
    (u : EuclideanSpace ℝ (Fin d)) (lam : ∀ j, Fin (H j).length → ℝ)
    (hlam : ∀ j, PredictsWith ϵ T (H j) u (lam j)) :
    commitPrice T Cb H lam ∈ Set.Icc (inner ℝ θ u - 1 / (4 * (T : ℝ))) (inner ℝ θ u) := by sorry

end RobustCtxPricing
