-- Prove2me | Theorems.Thm_RandGraphStates_theorem_2_4
-- name    : RandGraphStates.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:31.032336+00:00
-- url     : https://prove2.me/theorems/1e7b8c7d-c85c-49e8-8555-097c2e6b1ac6
-- title:
--   Theorem 2.4: $\alpha_{\mathrm{LC}}(G_{n,p})$ lies between $(c_{\mathrm{low}}-o(1))\sqrt n$ and $(\sqrt{2\log_23}+o(1))\sqrt n$
-- statement:
--   Let $p=p(n)\in(0,1)$ and $p_-:=\min\{p,1-p\}$. Let $x_0\in(0,1/2)$ be the solution of $1-H(x_0)=x_0/8$, where $H$ is the entropy in bits, and set $c_{\mathrm{low}}:=\sqrt{x_0}/2\approx0.3056$.
--
--   1. If $p_-\ge\log n/\sqrt n$, then with high probability $\alpha_{\mathrm{LC}}(G_{n,p})\ge(c_{\mathrm{low}}-o(1))\sqrt n$.
--   2. If $\dfrac{p_-^3\sqrt n}{\log(e/p_-)\log n}\to\infty$, then with high probability $\alpha_{\mathrm{LC}}(G_{n,p})\le\bigl(\sqrt{2\log_23}+o(1)\bigr)\sqrt n$.
--   3. In particular, for every constant $p\in(0,1)$, with high probability
--   $$
--   \alpha_{\mathrm{LC}}(G_{n,p})=\Theta(\sqrt n).
--   $$
--
--   Here $\alpha_{\mathrm{LC}}(G)$ is the largest independence number in the local-complementation orbit of $G$. For the graph state $|G\rangle$, $n-\alpha_{\mathrm{LC}}(G)$ is the Pauli persistency, so the theorem fixes the Pauli persistency of random graph states at $n-\Theta(\sqrt n)$.
--
--   Differences from the source:
--   - reading: p₋ ≥ log n/√n → the inequality for all large n (∀ᶠ n); reason: for all n it is unsatisfiable (at n = 7, log n/√n ≈ 0.735 > 1/2 ≥ p₋), so the clause would be empty; the eventual form is the weaker hypothesis and implies the literal one
--   - reading: unsubscripted log in the hypothesis on p₋ → natural logarithm Real.log; reason: the proofs use |q| ≤ e^(−2p₋) and log(e/p₋); natural log gives the weaker hypothesis, so the stronger theorem, which implies the base-2 reading
--   - encoding: (c_low − o(1))√n and (√(2 log₂ 3) + o(1))√n → every fixed c < √x₀/2 in (i), every fixed c > √(2 log₂ 3) in (ii); reason: equivalent by a diagonal argument; Theorems 4.20 and 4.17 are stated and proved this way
--   - reading: Θ(√n) for every constant p → ∃ c₁ c₂ > 0 before p; reason: clauses (i) and (ii) give absolute constants; this is the stronger reading
--   - encoding: p = p(n), with high probability → p : ℕ → ℝ with p n ∈ (0, 1) for all n; Pr → 1 by Tendsto of gnpProb; reason: the definition of whp on p.5
--   - encoding: x₀, the solution of 1 − H(x₀) = x₀/8 → ∀ x₀ ∈ (0, 1/2) with that equation; reason: the equation has exactly one solution in (0, 1/2), proved in the verification file; "≈ 0.3056" is a remark
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Theorem 2.4, p.6

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Theorem 2.4.** Let `p = p(n) ∈ (0, 1)` and `p₋ := min{p, 1 - p}`. Let `x₀ ∈ (0, 1/2)` be the solution of
`1 - H(x₀) = x₀/8`, and set `c_low := √x₀/2 ≈ 0.3056`.
(i) If `p₋ ≥ log n/√n`, then with high probability `αLC(G_{n,p}) ≥ (c_low - o(1))√n`.
(ii) If `p₋³√n/(log(e/p₋) log n) → ∞`, then with high probability `αLC(G_{n,p}) ≤ (√(2 log₂ 3) + o(1))√n`.
In particular, for every constant `p ∈ (0, 1)`, with high probability `αLC(G_{n,p}) = Θ(√n)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Theorem 2.4, p.6.

**Formalization Note.** The `o(1)` are unfolded: every fixed `c < c_low` in (i), every fixed `c > √(2 log₂ 3)` in (ii); by a
diagonal argument these are equivalent to the printed forms. The hypothesis of (i) holds for all large `n`; for all `n` it
would be unsatisfiable (at `n = 7`, `log n/√n > 1/2 ≥ p₋`). `H` is in bits (the published `SquashedKey.h₂`), `log` is natural. `x₀` is bound by its equation,
which has exactly one solution in `(0, 1/2)` (`Solutions/verification/RandGraphStates_Sanity.lean`). The `Θ` constants are
absolute: `∃ c₁ c₂` comes before `p`. "With high probability" is `Pr → 1`. -/
theorem theorem_2_4 :
    (∀ p : ℕ → ℝ, (∀ n, 0 < p n ∧ p n < 1) →
      (∀ᶠ n : ℕ in atTop, Real.log n / Real.sqrt n ≤ pMinus (p n)) →
      ∀ x0 : ℝ, 0 < x0 → x0 < 1 / 2 → 1 - SquashedKey.h₂ x0 = x0 / 8 →
      ∀ c : ℝ, c < Real.sqrt x0 / 2 →
      Tendsto (fun n : ℕ => gnpProb n (p n) (fun G => c * Real.sqrt n ≤ (alphaLC G : ℝ)))
        atTop (𝓝 1)) ∧
    (∀ p : ℕ → ℝ, (∀ n, 0 < p n ∧ p n < 1) →
      Tendsto (fun n : ℕ => pMinus (p n) ^ 3 * Real.sqrt n /
        (Real.log (Real.exp 1 / pMinus (p n)) * Real.log n)) atTop atTop →
      ∀ c : ℝ, Real.sqrt (2 * Real.logb 2 3) < c →
      Tendsto (fun n : ℕ => gnpProb n (p n) (fun G => (alphaLC G : ℝ) ≤ c * Real.sqrt n))
        atTop (𝓝 1)) ∧
    (∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ p : ℝ, 0 < p → p < 1 →
      Tendsto (fun n : ℕ => gnpProb n p (fun G =>
          c1 * Real.sqrt n ≤ (alphaLC G : ℝ) ∧ (alphaLC G : ℝ) ≤ c2 * Real.sqrt n))
        atTop (𝓝 1)) := by sorry

end RandGraphStates
