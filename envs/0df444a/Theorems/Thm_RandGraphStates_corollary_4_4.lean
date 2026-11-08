-- Prove2me | Theorems.Thm_RandGraphStates_corollary_4_4
-- name    : RandGraphStates.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:15.433634+00:00
-- url     : https://prove2.me/theorems/e848fbee-d2e1-40ae-b3e4-39828b7edd44
-- title:
--   Corollary 4.4: uniform nullity tail
-- statement:
--   Let $A_k(1/2)$ be the adjacency matrix over $\mathbb F_2$ of a uniform random graph on $k$ vertices. If $t\equiv k\pmod 2$, then
--   $$
--   \Pr\bigl(\mathrm{Nullity}(A_k(1/2))\ge t\bigr)=C_{\mathrm{unif}}\,2^{-\binom t2}\bigl(1+O(2^{-t}+2^{-(k-t)})\bigr),
--   $$
--   and, with no parity restriction, for every $t\ge0$,
--   $$
--   \Pr\bigl(\mathrm{Nullity}(A_k(1/2))\ge t\bigr)\le C_{\mathrm{unif}}\,2^{-\binom t2}.
--   $$
--   This is the reference tail against which every $p$-biased estimate in the mission is compared.
--
--   Differences from the source:
--   - encoding: O(2^{−t} + 2^{−(k−t)}) → ∃ C before k and t, and a real e with |e| ≤ C(2^{−t} + 2^{−(k−t)}), integer exponents; reason: the implied constant is absolute; integer exponents keep t > k meaningful without truncation
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Corollary 4.4, p.19

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

/-- **Corollary 4.4** (uniform nullity tail). If `t ≡ k (mod 2)`, then
`Pr(Nullity(A_k(1/2)) ≥ t) = C_unif 2^{-C(t,2)} (1 + O(2^{-t} + 2^{-(k-t)}))`, and for every `t ≥ 0`,
`Pr(Nullity(A_k(1/2)) ≥ t) ≤ C_unif 2^{-C(t,2)}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Corollary 4.4, p.19.

**Formalization Note.** The implied constant is absolute: `∃ C` comes before `k` and `t`. The exponents
are integers, so `t > k` needs no exclusion. -/
theorem corollary_4_4 :
    (∃ C : ℝ, ∀ k t : ℕ, t ≡ k [MOD 2] →
      ∃ e : ℝ, |e| ≤ C * ((2 : ℝ) ^ (-(t : ℤ)) + (2 : ℝ) ^ (-((k : ℤ) - (t : ℤ)))) ∧
        gnpProb k (1 / 2) (fun G => t ≤ nullity (adjF2 G)) =
          Cunif * (2 : ℝ) ^ (-((t.choose 2 : ℕ) : ℤ)) * (1 + e)) ∧
    (∀ k t : ℕ,
      gnpProb k (1 / 2) (fun G => t ≤ nullity (adjF2 G)) ≤
        Cunif * (2 : ℝ) ^ (-((t.choose 2 : ℕ) : ℤ))) := by sorry

end RandGraphStates
