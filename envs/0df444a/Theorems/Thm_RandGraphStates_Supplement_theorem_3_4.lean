-- Prove2me | Theorems.Thm_RandGraphStates_Supplement_theorem_3_4
-- name    : RandGraphStates.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:22:22.92573+00:00
-- url     : https://prove2.me/theorems/e6cf83c6-8816-4cd7-a910-57734d2de27c
-- title:
--   Theorem 3.4, p.10 — every graph on $n$ vertices has $\delta_{\mathrm{LC}}(G)\le\beta n+o(n)$, $\beta$ the optimum of an MRRW program
-- statement:
--   Let $H$ be the entropy function in bits and let $\beta$ be the optimal value of the program
--   $$
--   \begin{aligned}
--   \text{minimize}\quad&\frac{3\delta(1+2\gamma)}{4}\\
--   \text{subject to}\quad&H\Bigl(\frac12-\sqrt{\delta(1-\delta)}\Bigr)=\frac{4\gamma}{3+6\gamma},\qquad \delta,\gamma\in[0,1/2].
--   \end{aligned}
--   $$
--   Then every graph $G$ on $n$ vertices satisfies
--   $$
--   \delta_{\mathrm{LC}}(G)\le\beta n+o(n),
--   $$
--   with the $o(n)$ term depending only on $n$: for every $\varepsilon>0$ there is $N$ such that every graph on $n\ge N$ vertices has $\delta_{\mathrm{LC}}(G)\le(\beta+\varepsilon)n$.
--
--   The program is feasible ($\delta=1/2$, $\gamma=0$ gives the value $3/8$) and its minimum is attained; numerically $\beta\approx0.3413$, which yields Theorem 2.1.
--
--   **Formalization Note** $\beta$ is bound as the least element of the set of feasible objective values; the sanity file proves that this least element exists. $H$ is the published `SquashedKey.h₂`.
--
--   Differences from the source:
--   - encoding: β the solution of the optimization problem → every β that is the least feasible objective value; reason: the minimum exists and is unique, so this is the printed β
--   - encoding: δLC(G) ≤ βn + o(n) for a graph G on n vertices → ∀ ε > 0 ∃ N ∀ n ≥ N ∀ G on n vertices, δLC(G) ≤ (β + ε)n; reason: the o(n) term is a function of n alone, which is this unfolding
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Theorem 3.4, p.10; proof pp.10–11

import Mathlib
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_RandGraphStates_Supplement_deltaLC

set_option autoImplicit false

namespace RandGraphStates.Supplement

/-- **Theorem 3.4.** Let `G` be a graph on `n` vertices. Then `δLC(G) ≤ βn + o(n)`, where `β` is
the solution to the optimization problem
  minimize `3δ(1 + 2γ)/4` subject to `H(1/2 - √(δ(1 - δ))) = 4γ/(3 + 6γ)` for `δ, γ ∈ [0, 1/2]`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), Theorem 3.4, p.10.

**Formalization Note.** `β` is bound as the least element of the set of feasible values
`3δ(1 + 2γ)/4`. The feasible set is nonempty (`δ = 1/2, γ = 0`, value `3/8`) and compact, so the
least element exists and is the printed minimum
(`Solutions/verification/RandGraphStates_Supplement_Sanity.lean`). `H` is the entropy function in
bits, the published `SquashedKey.h₂`. The `o(n)` is uniform over graphs on `n` vertices and is
unfolded: every `ε > 0` has an `N` with `δLC(G) ≤ (β + ε)n` for every graph on `n ≥ N` vertices.
The sentence after the theorem ("A numerical estimate shows that `β ≈ 0.3413` …") is a numerical
comment, not a clause, and is not formalized (Theorem 2.1 states the `0.3413` bound). -/
theorem theorem_3_4 :
    ∀ β : ℝ, IsLeast {v : ℝ | ∃ δ γ : ℝ, 0 ≤ δ ∧ δ ≤ 1 / 2 ∧ 0 ≤ γ ∧ γ ≤ 1 / 2 ∧
        SquashedKey.h₂ (1 / 2 - Real.sqrt (δ * (1 - δ))) = 4 * γ / (3 + 6 * γ) ∧
        v = 3 * δ * (1 + 2 * γ) / 4} β →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n),
      (deltaLC G : ℝ) ≤ (β + ε) * n := by sorry

end RandGraphStates.Supplement
