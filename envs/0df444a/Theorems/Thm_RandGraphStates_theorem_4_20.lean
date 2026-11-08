-- Prove2me | Theorems.Thm_RandGraphStates_theorem_4_20
-- name    : RandGraphStates.theorem_4_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:44.909193+00:00
-- url     : https://prove2.me/theorems/d8134b7c-7bb7-42a6-b100-1006f13c9019
-- title:
--   Theorem 4.20: lower bound on $\alpha_{\mathrm{LC}}(G_{n,p})$
-- statement:
--   Let $x_0\in(0,1/2)$ be the solution of $1-H(x_0)=x_0/8$, and put $c_{\mathrm{low}}:=\sqrt{x_0}/2\approx0.305568$. For every fixed $c<c_{\mathrm{low}}$, if $p_-\ge\log n/\sqrt n$, then with high probability,
--   $$
--   \alpha_{\mathrm{LC}}(G_{n,p})\ge c\sqrt n .
--   $$
--   This is clause (i) of the goal theorem, with no restriction to $p\le1/2$.
--
--   Differences from the source:
--   - reading: p₋ ≥ log n/√n → the inequality for all large n (∀ᶠ n); reason: for all n it is unsatisfiable (at n = 7, log n/√n ≈ 0.735 > 1/2 ≥ p₋), so the clause would be empty; the eventual form is the weaker hypothesis and implies the literal one
--   - reading: unsubscripted log in the hypothesis on p₋ → natural logarithm Real.log; reason: the proofs use |q| ≤ e^(−2p₋) and log(e/p₋); natural log gives the weaker hypothesis, so the stronger theorem, which implies the base-2 reading
--   - encoding: p = p(n), with high probability → p : ℕ → ℝ with p n ∈ (0, 1) for all n; Pr → 1 by Tendsto of gnpProb; reason: the definition of whp on p.5
--   - encoding: x₀, the solution of 1 − H(x₀) = x₀/8 → ∀ x₀ ∈ (0, 1/2) with that equation; reason: the equation has exactly one solution in (0, 1/2), proved in the verification file; "≈ 0.305568" is a remark
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Theorem 4.20, p.35

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

/-- **Theorem 4.20** (lower bound). Let `x₀ ∈ (0, 1/2)` be the solution of `1 - H(x₀) = x₀/8` and `c_low := √x₀/2`.
For every fixed `c < c_low`, if `p₋ ≥ log n/√n`, then with high probability `αLC(G_{n,p}) ≥ c√n`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Theorem 4.20, p.35.

**Formalization Note.** `p = p(n) ∈ (0, 1)`, with no restriction to `p ≤ 1/2`. The hypothesis on `p₋` holds for all large
`n`; for all `n` it would be unsatisfiable (at `n = 7`, `log n/√n > 1/2 ≥ p₋`). `H` is in bits (the published `SquashedKey.h₂`), `log` is natural. `x₀` is bound by
its equation, which has exactly one solution in `(0, 1/2)` (`Solutions/verification/RandGraphStates_Sanity.lean`). -/
theorem theorem_4_20 (p : ℕ → ℝ) (hp : ∀ n, 0 < p n ∧ p n < 1)
    (hpn : ∀ᶠ n : ℕ in atTop, Real.log n / Real.sqrt n ≤ pMinus (p n))
    (x0 : ℝ) (hx0 : 0 < x0) (hx1 : x0 < 1 / 2) (hxe : 1 - SquashedKey.h₂ x0 = x0 / 8)
    (c : ℝ) (hc : c < Real.sqrt x0 / 2) :
    Tendsto (fun n : ℕ => gnpProb n (p n) (fun G => c * Real.sqrt n ≤ (alphaLC G : ℝ)))
      atTop (𝓝 1) := by sorry

end RandGraphStates
