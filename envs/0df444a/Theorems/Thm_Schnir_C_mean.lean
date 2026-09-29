-- Prove2me | Theorems.Thm_Schnir_C_mean
-- name    : Schnir.C_mean
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:47:52.324462+00:00
-- url     : https://prove2.me/theorems/c1e99a66-33e7-43ed-abd4-8881d9e60752
-- title:
--   Mean square of the arithmetic factor: $\sum_{s\le x,\,2\mid s} C(s)^2\le \tfrac{21}{2}x$
-- statement:
--   For every real $x\ge 0$,
--
--   $$
--   \sum_{\substack{1\le s\le x\\ s \text{ even}}} C(s)^2 \;\le\; \frac{21}{2}\,x,
--   \qquad C(s)=\prod_{p\mid s}\left(1+\frac{p}{(p-1)^2}\right).
--   $$
--
--   This controls the average size of the arithmetic factor in the pointwise sieve bound, which is what the second moment needs.
--
--   **Formalization Note** The sum is over even integers $1\le s\le\lfloor x\rfloor$.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (12), §3

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

theorem C_mean (x : ℝ) (hx : 0 ≤ x) :
    ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, (C s) ^ 2 ≤ 21 / 2 * x := by sorry

end Schnir
