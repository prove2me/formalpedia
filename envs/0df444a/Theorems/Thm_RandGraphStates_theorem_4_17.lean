-- Prove2me | Theorems.Thm_RandGraphStates_theorem_4_17
-- name    : RandGraphStates.theorem_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:24.307559+00:00
-- url     : https://prove2.me/theorems/3fc3776d-29b9-4c3f-85d0-32faffed968e
-- title:
--   Theorem 4.17: upper bound on $\alpha_{\mathrm{LC}}(G_{n,p})$
-- statement:
--   Suppose
--   $$
--   \frac{p_-^3\sqrt n}{\log(e/p_-)\log n}\longrightarrow\infty .
--   $$
--   Then, with high probability,
--   $$
--   \alpha_{\mathrm{LC}}(G_{n,p})\le\bigl(\sqrt{2\log_23}+o(1)\bigr)\sqrt n .
--   $$
--   This is clause (ii) of the goal theorem. The formal statement is for each fixed $c>\sqrt{2\log_23}$.
--
--   Differences from the source:
--   - encoding: (√(2 log₂ 3) + o(1))√n → every fixed c > √(2 log₂ 3), Pr[αLC ≤ c√n] → 1; reason: equivalent by a diagonal argument; the proof runs this way ("Fix ε > 0")
--   - encoding: p = p(n), with high probability → p : ℕ → ℝ with p n ∈ (0, 1) for all n; Pr → 1 by Tendsto of gnpProb; reason: the definition of whp on p.5
--   - encoding: unsubscripted log in the hypothesis → natural logarithm; reason: the limit +∞ does not depend on the base
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Theorem 4.17, p.31

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

/-- **Theorem 4.17** (upper bound). If `p₋³ √n / (log(e/p₋) log n) → ∞`, then with high probability
`αLC(G_{n,p}) ≤ (√(2 log₂ 3) + o(1)) √n`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Theorem 4.17, p.31.

**Formalization Note.** `p = p(n) ∈ (0, 1)`. `(√(2 log₂ 3) + o(1))` is unfolded as every fixed `c > √(2 log₂ 3)`, as the
proof does ("Fix `ε > 0`"); by a diagonal argument the two forms are equivalent. "With high probability" is
`Pr → 1`. `log` is natural. -/
theorem theorem_4_17 (p : ℕ → ℝ) (hp : ∀ n, 0 < p n ∧ p n < 1)
    (hpn : Tendsto (fun n : ℕ => pMinus (p n) ^ 3 * Real.sqrt n /
      (Real.log (Real.exp 1 / pMinus (p n)) * Real.log n)) atTop atTop)
    (c : ℝ) (hc : Real.sqrt (2 * Real.logb 2 3) < c) :
    Tendsto (fun n : ℕ => gnpProb n (p n) (fun G => (alphaLC G : ℝ) ≤ c * Real.sqrt n))
      atTop (𝓝 1) := by sorry

end RandGraphStates
