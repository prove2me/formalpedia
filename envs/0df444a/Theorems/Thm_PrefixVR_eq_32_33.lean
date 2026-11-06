-- Prove2me | Theorems.Thm_PrefixVR_eq_32_33
-- name    : PrefixVR.eq_32_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:50.315262+00:00
-- url     : https://prove2.me/theorems/c9287994-13a9-41d2-9885-2401d703720a
-- title:
--   Eqs. (32)–(33) — error of the completed prefix
-- statement:
--   Suppose condition (2) holds with constant $\delta$, and run Algorithm 1 with stepsize $\eta$ from $x_1$. For a cycle $s$ and a position $1\le m\le n$ write
--   $$
--   a_{s,m}=h_{s,m}-P_m(x_{sn+m+1}),\qquad S_u=\mathbb E\|x_{u+1}-x_u\|^2 ,
--   $$
--   where $h_{s,m}$ is the prefix accumulator after update $sn+m$ and $P_m$ the prefix gradient. Then
--
--   1. $\displaystyle\mathbb E\|a_{s,m}\|^2\le\delta^2\sum_{u=sn+1}^{sn+m}S_u$ for $1\le m\le n$ (32);
--   2. since $P_n=\nabla f$: $\displaystyle\mathbb E\|h_{s,n}-\nabla f(x_{(s+1)n+1})\|^2\le\delta^2\sum_{u=sn+1}^{(s+1)n}S_u$ (33).
--
--   Both are stated for every cycle whose times lie within the horizon $T$ of the run ($sn+m\le T$, resp. $(s+1)n\le T$), every stepsize and every initial point. The expectation is over all draws.
--
--   The completed prefix replaces the active estimate at the end of each cycle (7), so (33) is the error the next cycle starts from.
--
--   **Formalization Note** The maps $g_i$ stand for $\nabla f_i$ and $\nabla f$ for their average; no smoothness is assumed, since the proof uses only (2).
--
--   Differences from the source:
--   - generalization: the component gradients ∇fᵢ of differentiable fᵢ, with ∇f their average in (2) → arbitrary maps g i : ℝᵈ → ℝᵈ satisfying (2) with ∇f replaced by the average (1/n)∑ g i; reason: the statement and its proof use only (2); taking g i = ∇fᵢ, whose average is ∇f, gives the source's statement
--   - generalization: stepsize η > 0 (input of Algorithm 1) → any real η; reason: the bound holds for every η; restricting to η > 0 gives the source's statement
--   - encoding: the expectation over the estimator samples of the run of Algorithm 1 → the uniform average over the finite sample space Sample n T (output index τ and the draws (j_t, i_t) of updates t ≤ T, with one-point or unused dummy draws where the paper draws nothing), for a horizon T containing every time in the statement; reason: independent uniform draws on finite sets have the uniform product law; unused coordinates and later draws change no expectation of quantities up to the stated times
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. B, "Error of a prefix update", Eqs. (27), (32), (33), pp.13–14 (PDF pp.13–14)

import Mathlib
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_prefixGrad
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **Error of the completed prefix, (32)–(33).** Jiang, Wang, Yang, Li, Zhang (manuscript,
sha256 ed33106a…), App. B, "Error of a prefix update", Eqs. (32)–(33), p.14: with
`a_{s,r} := h_{s,r} − P_r(x_{sn+r+1})` (27) and `S_u = 𝔼‖x_{u+1} − x_u‖²`,
`𝔼‖a_{s,m}‖² ≤ δ² ∑_{u=sn+1}^{sn+m} S_u` for `1 ≤ m ≤ n` (32), and, since `P_n = ∇f`,
`𝔼‖h_{s,n} − ∇f(x_{(s+1)n+1})‖² ≤ δ² ∑_{u=sn+1}^{(s+1)n} S_u` (33).

Stated for Algorithm 1 with horizon `T`, every stepsize `η` and initial point `x₁`, for every
cycle position with `sn + m ≤ T` (all times inside the horizon).

**Formalization Note.** `g i` stands for `∇fᵢ` and (2) is `Variation g δ`, with `∇f` the average
`gradAvg g` of the `g i`; no smoothness is assumed (the proof uses only (2)). `h_{s,m}` is the
accumulator after update `sn + m` (`hAfter`), `P_m` is `prefixGrad g m`, the expectation is over
`Sample n T` (`expect`), and `S_u` is `moveEnergy`. Components are `Fin n` with `NeZero n`. -/
theorem eq_32_33 {n d : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hvar : Variation g δ) (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    (∀ s m : ℕ, 1 ≤ m → m ≤ n → s * n + m ≤ T →
      expect (fun ω : Sample n T =>
          ‖hAfter g η x₁ ω (s * n + m) - prefixGrad g m (xIter g η x₁ ω (s * n + m + 1))‖ ^ 2)
        ≤ δ ^ 2 * ∑ u ∈ Finset.Icc (s * n + 1) (s * n + m), moveEnergy g η x₁ T u) ∧
    (∀ s : ℕ, (s + 1) * n ≤ T →
      expect (fun ω : Sample n T =>
          ‖hAfter g η x₁ ω ((s + 1) * n) - gradAvg g (xIter g η x₁ ω ((s + 1) * n + 1))‖ ^ 2)
        ≤ δ ^ 2 * ∑ u ∈ Finset.Icc (s * n + 1) ((s + 1) * n), moveEnergy g η x₁ T u) := by sorry

end PrefixVR
