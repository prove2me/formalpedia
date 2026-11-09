-- Prove2me | Theorems.Thm_WeightedEdgeColor_proposition_A_4
-- name    : WeightedEdgeColor.proposition_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:44:52.27404+00:00
-- url     : https://prove2.me/theorems/6eb17c02-91b9-468f-8dfa-f7132687a84b
-- title:
--   Proposition A.4 — controlling many sums of independent choices (Harris–Srinivasan)
-- statement:
--   Let $Z_i$ be independent random choices, each with a finite set of possible values. For each index $t$ let
--   $$
--   F_t=\sum_i f_{t,i}(Z_i),\qquad 0\le f_{t,i}(z)\le 1 .
--   $$
--   Put
--   $$
--   R=\max_t\mathbb E F_t,\qquad D=\max_{i,z}\sum_t f_{t,i}(z),\qquad C=\max\{2,R,D\}.
--   $$
--   There is an absolute constant $K$ such that some choice of all the $Z_i$ satisfies, for every $t$ simultaneously,
--   $$
--   F_t\le \mathbb E F_t+K\Big(\sqrt{R\log(C+2)}+\log(C+2)\Big).
--   $$
--
--   Here $R$ bounds the mean of one sum and $D$ the combined contribution of one choice to all sums; neither counts the number of sums, which is what makes the rounding errors in Theorem 3.1 independent of the number of vertices. This is a form of Theorem 4.7 of Harris and Srinivasan, imported by the paper.
--
--   **Formalization Note** The choice $Z_i$ ranges over a finite type $\Omega_i$ of values, each with positive probability $p_i(\omega)$, and $\mathbb E F_t=\sum_i\sum_\omega p_i(\omega)f_{t,i}(\omega)$. The index sets of $i$ and $t$ are finite. $R$ and $D$ enter as upper bounds on $\mathbb EF_t$ and on $\sum_t f_{t,i}(\omega)$; $K$ is chosen before all data.
--
--   Differences from the source:
--   - encoding: $R=\max_t\mathbb EF_t$, $D=\max_{i,z}\sum_tf_{t,i}(z)$ → any $R\ge\mathbb EF_t$ for all $t$ and $D\ge\sum_tf_{t,i}(\omega)$ for all $i,\omega$; reason: the bound is nondecreasing in $R$ and $D$, and taking $R$, $D$ equal to the maxima gives the printed statement
--   - encoding: independent random choices with finite sets of possible values → finite value types with positive probabilities and $\mathbb EF_t$ written as the double sum; reason: the expectation of a sum of functions of single coordinates is this sum; the possible values are the values of positive probability
--   - reading: index sets of $i$ and $t$ unstated → finite; reason: the maxima and sums presuppose it, and since the space of all choices is finite an infinite family of sums would reduce to its finite subfamilies
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Proposition A.4, p.26 (citing Harris–Srinivasan [HS19, Theorem 4.7])

import Mathlib

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Proposition A.4 (Controlling many sums, Harris–Srinivasan [HS19, Theorem 4.7]).

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Proposition A.4, p.26. Imported result; the paper derives this form from [HS19, Theorem 4.7].

**Formalization Note.** The independent choices `Z_i` take values in finite types `Ω i` with
laws `p i`; `Ω i` is the set of possible values, so every value has positive probability. The
expectation of `F_t = ∑_i f_{t,i}(Z_i)` is `∑_i ∑_ω p_i(ω) f_{t,i}(ω)` (linearity). The maxima
`R = max_t 𝔼F_t` and `D = max_{i,z} ∑_t f_{t,i}(z)` are taken as upper bounds `R`, `D`; the
bound is monotone in `R` and `D`, so this is equivalent to the printed maxima. `C = max{2,R,D}`.
The absolute constant `K` of `O(·)` is chosen before everything else. -/
theorem proposition_A_4 :
    ∃ K : ℝ, ∀ (I T : Type) [Fintype I] [Fintype T] (Ω : I → Type) [∀ i, Fintype (Ω i)]
      (p : ∀ i, Ω i → ℝ) (f : T → ∀ i, Ω i → ℝ) (R D : ℝ),
      (∀ i ω, 0 < p i ω) → (∀ i, ∑ ω, p i ω = 1) →
      (∀ t i ω, 0 ≤ f t i ω ∧ f t i ω ≤ 1) →
      (∀ t, ∑ i, ∑ ω, p i ω * f t i ω ≤ R) →
      (∀ i ω, ∑ t, f t i ω ≤ D) →
      ∃ z : ∀ i, Ω i, ∀ t, ∑ i, f t i (z i) ≤ ∑ i, ∑ ω, p i ω * f t i ω +
        K * (Real.sqrt (R * Real.log (max 2 (max R D) + 2)) + Real.log (max 2 (max R D) + 2)) := by sorry

end WeightedEdgeColor
