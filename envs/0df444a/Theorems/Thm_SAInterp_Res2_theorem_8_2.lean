-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_8_2
-- name    : SAInterp.Res2.theorem_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:40:31.52643+00:00
-- url     : https://prove2.me/theorems/d72bfb0d-3424-4036-a04f-37483ebf63f9
-- title:
--   Theorem 8.2 — CPLS^bool_n ∘ ⊕ (n = 2^ℓ, ℓ large): polynomial-size Res(2) refutations, dual-variable SA size 2^Ω(n)
-- statement:
--   There are constants $C$, $c>0$ and $\ell_0$ such that for every $\ell\ge\ell_0$ and $n=2^\ell$:
--   - $\mathrm{CPLS}^{\mathrm{bool}}_n\circ\oplus$ has a $\mathrm{Res}(2)$ refutation of size at most $C\,n^C+C$;
--   - every Sherali-Adams refutation of $\mathrm{CPLS}^{\mathrm{bool}}_n\circ\oplus$ in the dual-variable encoding has size at least $2^{c\,n}$.
--
--   Since $\mathrm{CPLS}_n$ has $O(n^3)$ variables, this gives Theorem 1.1.
--
--   Differences from the source:
--   - reading: "ℓ sufficiently large", polynomial size, 2^{Ω(n)} → ∃ C, c > 0, ℓ0, ∀ ℓ ≥ ℓ0, size ≤ C · n^C + C and ≥ 2^{c n}; reason: explicit constants fixed before ℓ.
--   - reading: Res(2) size = total number of symbols → Σ over lines of (1 + literal occurrences); reason: within a constant factor of any symbol count.
--   - reading: SA size, "the (maximum) number of monomials … before cancellations" → total number of monomials of all expanded products; reason: the readings differ by a factor polynomial in n, same statement under ∃ c.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 44 (PDF p. 46), Theorem 8.2

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_ResK
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 8.2 (p. 44): there are constants `C`, `c > 0` and `ℓ0` such that for every
`ℓ ≥ ℓ0` and `n = 2^ℓ`, `CPLS^bool_n ∘ ⊕` has a `Res(2)` refutation of size `≤ C · n^C + C`,
and every Sherali-Adams refutation of it in the dual-variable encoding has size `≥ 2^{c n}`. -/
theorem theorem_8_2 :
    ∃ C c : ℝ, 0 < c ∧ ∃ ℓ0 : ℕ, ∀ ℓ : ℕ, ℓ0 ≤ ℓ →
      (∃ Q : List (DNF (BoolVar (cplsBits ℓ) ⊕ BoolVar (cplsBits ℓ))),
        IsResKRefutation 2 (xorCNF (CPLSbool ℓ)) Q ∧
          (resKSize Q : ℝ) ≤ C * ((2 : ℝ) ^ ℓ) ^ C + C) ∧
      ∀ π : SARefutation (xorCNF (CPLSbool ℓ)),
        (2 : ℝ) ^ (c * (2 : ℝ) ^ ℓ) ≤ (π.size : ℝ) := by sorry

end SAInterp.Res2
