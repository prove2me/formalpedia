-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_8_5
-- name    : SAInterp.Res2.theorem_8_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:40:36.269286+00:00
-- url     : https://prove2.me/theorems/15de1cd2-8c71-440c-9bd8-c21072f0ea72
-- title:
--   Theorem 8.5 — polynomial-size Res(2) refutations of CPLS^bool_n ∘ ⊕
-- statement:
--   There is a constant $C$ such that for every positive integer $\ell$ and $n=2^\ell$, the formula $\mathrm{CPLS}^{\mathrm{bool}}_n\circ\oplus$ has a $\mathrm{Res}(2)$ refutation $\Pi$ with
--   $$\mathrm{size}(\Pi)\ \le\ C\,n^{C}+C .$$
--   The paper derives it from Theorem 8.4 and the cited polynomial-size, width-$O(\log n)$ Resolution refutations of $\mathrm{CPLS}^{\mathrm{bool}}_n$ ([KST07], [DR23]).
--
--   Differences from the source:
--   - reading: polynomial-size → ≤ C · n^C + C with one constant C for all n = 2^ℓ, ℓ ≥ 1; reason: the standard meaning, with the constant fixed before n.
--   - reading: Res(2) size = total number of symbols → Σ over lines of (1 + literal occurrences); reason: within a constant factor of any symbol count.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 46 (PDF p. 48), Theorem 8.5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_ResK
import Definitions.Def_SAInterp_Res2_Indicator
import Definitions.Def_SAInterp_Res2_CPLS

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 8.5 (p. 46): `CPLS^bool_n ∘ ⊕` has polynomial-size `Res(2)` refutations: there is a
constant `C` such that for every positive integer `ℓ` and `n = 2^ℓ` it has a `Res(2)` refutation
of size `≤ C · n^C + C`. -/
theorem theorem_8_5 :
    ∃ C : ℝ, ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∃ Q : List (DNF (BoolVar (cplsBits ℓ) ⊕ BoolVar (cplsBits ℓ))),
        IsResKRefutation 2 (xorCNF (CPLSbool ℓ)) Q ∧
          (resKSize Q : ℝ) ≤ C * ((2 : ℝ) ^ ℓ) ^ C + C := by sorry

end SAInterp.Res2
