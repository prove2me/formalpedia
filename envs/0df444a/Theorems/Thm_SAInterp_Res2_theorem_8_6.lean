-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_8_6
-- name    : SAInterp.Res2.theorem_8_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:40:48.947636+00:00
-- url     : https://prove2.me/theorems/2c6e6535-6072-4676-b932-10918e2a988c
-- title:
--   Theorem 8.6 — every dual-variable Sherali-Adams refutation of CPLS^bool_n ∘ ⊕ has size 2^Ω(n)
-- statement:
--   There are constants $c>0$ and $N_0$ such that for every $n=2^\ell\ge N_0$, every Sherali-Adams refutation of $\mathrm{CPLS}^{\mathrm{bool}}_n\circ\oplus$ in the dual-variable encoding has size
--   $$\mathrm{size}\ \ge\ 2^{c\,n}.$$
--   This is the Sherali-Adams half of the separation. The paper proves it from Theorem 8.1 by a random restriction (a sketch).
--
--   Differences from the source:
--   - reading: 2^{Ω(n)} for any sufficiently large n → ∃ c > 0, ∃ N0, ∀ ℓ with 2^ℓ ≥ N0; reason: Ω with explicit constants fixed before n.
--   - reading: SA size, "the (maximum) number of monomials produced by expanding … before cancellations" → the total number of monomials of all expanded products; reason: p. 2 and the proof's union bound count all monomials; the two readings differ by a factor polynomial in n, so the statement with ∃ c is the same under both.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 46 (PDF p. 48), Theorem 8.6

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_ResK
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 8.6 (p. 46): there are `c > 0` and `N0` such that for every `n = 2^ℓ ≥ N0`, every
dual-variable Sherali-Adams refutation of `CPLS^bool_n ∘ ⊕` has size `≥ 2^{c n}`. -/
theorem theorem_8_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ ℓ : ℕ, N0 ≤ 2 ^ ℓ →
      ∀ π : SARefutation (xorCNF (CPLSbool ℓ)),
        (2 : ℝ) ^ (c * (2 : ℝ) ^ ℓ) ≤ (π.size : ℝ) := by sorry

end SAInterp.Res2
