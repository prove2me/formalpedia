-- Prove2me | Theorems.Thm_PlugInRisk_lemma_4_2
-- name    : PlugInRisk.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:41.500679+00:00
-- url     : https://prove2.me/theorems/ad753aba-7411-4f60-821c-5d1d53e4814c
-- title:
--   Lemma 4.2: AVaR of a Pareto variable
-- statement:
--   Let $q>1$ and let $X^*$ be Pareto distributed with scale parameter $1$ and shape parameter $q$. Then for every $u\in[0,1)$
--
--   $$
--   \mathrm{AVaR}_u(X^*)=\frac{q}{q-1}\cdot\frac{1}{(1-u)^{1/q}}.
--   $$
--
--   The explicit growth of $u\mapsto\mathrm{AVaR}_u(X^*)$ as $u\to1$ is what converts $q$-regularity into control of the spectral measures near $u=1$.
--
--   Differences from the source:
--
--   - generalization: the assumptions of Theorem 4.1 (1 < q ≤ p ≤ ∞, ρ q-regular, 𝒢 bounded, (a)/(b)) → only 1 < q; reason: the conclusion involves only q and X*; the source's hypotheses imply 1 < q
--   - encoding: X* a Pareto random variable → its law ν with IsPareto ν 1 q; reason: AVaR depends only on the law
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 4.2, p.18

import Mathlib
import Definitions.Def_PlugInRisk_avar
import Definitions.Def_PlugInRisk_IsPareto

open MeasureTheory

namespace PlugInRisk

/-- **Lemma 4.2** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 4.2, p.18): "Let X* be Pareto
distributed with scale parameter 1 and shape parameter q. Then we have that
AVaR_u(X*) = q/(q − 1) · 1/(1 − u)^{1/q} for every u ∈ [0, 1)."

**Formalization Note** Stated for the law `ν` of `X*` (AVaR depends on `X*` only through its
law). Of "the assumptions of Theorem 4.1" only `q > 1` enters the statement. -/
theorem lemma_4_2 (q : ℝ) (hq : 1 < q) (ν : Measure ℝ) (hν : IsPareto ν 1 q) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    avar ν u = q / (q - 1) * (1 / (1 - u) ^ (1 / q)) := by sorry

end PlugInRisk
