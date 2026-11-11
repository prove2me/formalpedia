-- Prove2me | Theorems.Thm_RandModSubsetSum_eq_54
-- name    : RandModSubsetSum.eq_54
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:28.427024+00:00
-- url     : https://prove2.me/theorems/a56352da-283d-4a3f-b45b-a73d359bfe91
-- title:
--   Equation (54) — the rounding loss satisfies $\eta<10^{-12}$
-- statement:
--   With the entropy-continuity modulus $f_q$ of Appendix A,
--
--   $$\eta=f_{686}(10^{-17})+124\big(f_{49}(10^{-17})+f_7(10^{-17})\big)<10^{-12}.$$
--
--   This bounds the total entropy-rate loss from rounding the nominal distributions to exact types, for every choice of pivot slots and root arrangement, once every full-stratum type is within $10^{-17}$ of its nominal distribution. It leaves the gap $\gamma-\eta\ge0.000001000025$ in (42).
--
--   Differences from the source: none.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Appendix A, (54), p. 57

import Mathlib
import Definitions.Def_RandModSubsetSum_RoundingLoss

namespace RandModSubsetSum

/-- **Equation (54)** (the rounding loss is below `10⁻¹²`). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Appendix A, (54), p. 57.

`η = f_{686}(10⁻¹⁷) + 124 (f_{49}(10⁻¹⁷) + f_7(10⁻¹⁷)) < 10⁻¹²`, with `f_q` of Appendix A, p. 56.

**Formalization Note.** The decimals are exact rationals. -/
theorem eq_54 :
    fq 686 (1 / 10 ^ 17) + 124 * (fq 49 (1 / 10 ^ 17) + fq 7 (1 / 10 ^ 17)) < 1 / 10 ^ 12 := by sorry

end RandModSubsetSum
