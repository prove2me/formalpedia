-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_8_1
-- name    : SAInterp.Res2.theorem_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:39:59.363683+00:00
-- url     : https://prove2.me/theorems/73cde9ba-bf4e-4c67-a4ce-ab14996e6f87
-- title:
--   Theorem 8.1 — SA(CPLS^bool_n) = Ω(n) for n = 2^ℓ
-- statement:
--   There is a constant $c>0$ such that for every positive integer $\ell$ and $n=2^\ell$, every Sherali-Adams refutation of $\mathrm{CPLS}^{\mathrm{bool}}_n$ in the dual-variable encoding has degree at least $c\,n$:
--   $$\mathrm{SA}(\mathrm{CPLS}^{\mathrm{bool}}_n)\ \ge\ c\,n .$$
--   Theorem 8.6 turns this degree bound into the size lower bound for $\mathrm{CPLS}^{\mathrm{bool}}_n\circ\oplus$.
--
--   Differences from the source:
--   - reading: SA(CPLS^bool_n) = Ω(n) → ∃ c > 0, ∀ ℓ ≥ 1, every SA refutation of CPLS^bool_{2^ℓ} has degree ≥ c · 2^ℓ; reason: Ω with an explicit constant, quantified over refutations (avoids sInf ∅ = 0); since every SA refutation of a formula without an empty clause has degree ≥ 1, this is equivalent to the "for all large n" form.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 44 (PDF p. 46), Theorem 8.1

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 8.1 (p. 44): `SA(CPLS^bool_n) = Ω(n)` for `n = 2^ℓ`, `ℓ` a positive integer: there is
a constant `c > 0` such that every Sherali-Adams refutation of `CPLS^bool_{2^ℓ}` has degree
`≥ c · 2^ℓ`, for every `ℓ ≥ 1`. -/
theorem theorem_8_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ π : SARefutation (CPLSbool ℓ), c * (2 : ℝ) ^ ℓ ≤ (π.degree : ℝ) := by sorry

end SAInterp.Res2
