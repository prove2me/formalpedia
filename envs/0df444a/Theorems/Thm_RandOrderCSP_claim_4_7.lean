-- Prove2me | Theorems.Thm_RandOrderCSP_claim_4_7
-- name    : RandOrderCSP.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:38.016236+00:00
-- url     : https://prove2.me/theorems/1a9a4e8b-75fe-4406-bf8d-63d86c7b7f1a
-- title:
--   Claim 4.7 — zero-label counts are Poisson and the streamed edges are i.i.d.
-- statement:
--   Consider the DIHP inputs of the gadget $(G_*,\mathcal Y_*)$ with parameters $\alpha>0$, $n\ge1$, $T$. Let $K_t$ be the set of edges of $H_t$ whose label row is zero, let $A_t=|K_t|$, and let player $t$ choose distinct $h_1,\dots,h_{m_1}\in K_t$ uniformly at random. Each $h$ is a copy of a unique edge $e$ of $G_*^n$. Take either the YES case conditioned on $\mathbf X=X$, with $p_e=\mathcal Y_*(j)(X|_e)$ for $e=(j,\tau)$, or the NO case, with $p_e=q^{-k}$. Then:
--
--   1. $A_1,\dots,A_T$ are independent Poisson random variables with mean $\alpha n^{-(k-1)}\sum_ep_e$.
--   2. For all values $a$ with every $a_t\ge m_1$ and all edge sequences $(e_{t,i})$,
--
--   $$\mathbb P\big[A=a,\ \text{the chosen edges are }(e_{t,i})\big]=\mathbb P[A=a]\prod_{t,i}\nu(e_{t,i}),\qquad \nu(e)=\frac{p_e}{\sum_{e'}p_{e'}}.$$
--
--   This is what makes the concatenated stream of the reduction a uniformly random ordering of its instance.
--
--   Differences from the source:
--   - encoding: conditioned on A_1, …, A_T the sequence is i.i.d. ν → the joint identity P[A = a ∧ sequence] = P[A = a] ∏ν; reason: same content without dividing by a null event
--   - generalization: the gadget (G∗, 𝒴∗) of Claim 4.5 and T, m₁, α as chosen in §4.3 → every gadget with nonempty vertex set and one-wise uniform coloring, every T, m₁, α > 0 and n ≥ 1; reason: the proof uses none of the §4.3 relations nor the gap instance; the source gadget and parameters are an instance
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Claim 4.7, p.19

import Mathlib
import Definitions.Def_RandOrderCSP_IsOneWiseUniform
import Definitions.Def_RandOrderCSP_DIHP

namespace RandOrderCSP

/-- **Claim 4.7 (the streamed constraints are i.i.d.).** Singer, Tulsiani, Velusamy, *A dichotomy theorem
for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Claim 4.7, p.19.

**Formalization Note.** `lab = some X` is the YES case conditioned on `𝐗 = X` and `lab = none` the NO
case; `zeroProb` is `p_e`. Item 1 gives the joint law of `(A_1, …, A_T)`: independent Poisson with mean
`αn^{-(k-1)} ∑_e p_e`. Item 2, "conditioned on `A = a`", is the joint identity
`P[A = a ∧ sequences = e] = P[A = a] ∏_{t,i} ν(e_t(i))`, which needs no division by a null event (when
`∑_e p_e = 0`, both sides vanish for `m₁ ≥ 1`). -/
theorem claim_4_7 {k q : ℕ} [NeZero q] (hk : 2 ≤ k) (hq : 2 ≤ q) {V E : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype E] [DecidableEq E] (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ)
    (hY : ∀ j, IsOneWiseUniform (Y j)) (α : ℝ) (hα : 0 < α) (n T m₁ : ℕ) (hn : 1 ≤ n)
    (lab : Option (V × Fin n → ZMod q)) :
    (∀ a : Fin T → ℕ, countProb G Y α n T lab a =
      ∏ t, ProbabilityTheory.poissonMeasure
        (α / (n : ℝ) ^ (k - 1) * ∑ e, zeroProb G Y n lab e).toNNReal {a t}) ∧
    (∀ (a : Fin T → ℕ) (e : Fin T → Fin m₁ → E × (Fin k → Fin n)), (∀ t, m₁ ≤ a t) →
      seqProb G Y α n T m₁ lab a e =
        countProb G Y α n T lab a *
          ∏ t, ∏ i, ENNReal.ofReal
            (zeroProb G Y n lab (e t i) / ∑ e', zeroProb G Y n lab e')) := by sorry

end RandOrderCSP
