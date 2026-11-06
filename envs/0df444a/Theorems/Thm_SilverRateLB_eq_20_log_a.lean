-- Prove2me | Theorems.Thm_SilverRateLB_eq_20_log_a
-- name    : SilverRateLB.eq_20_log_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:34.1982+00:00
-- url     : https://prove2.me/theorems/834bd22d-42cf-43fb-8b61-f80094dc8223
-- title:
--   (20) — $\log a=O(\eta^{-1}\log(1/\eta))$ under the choice (18)
-- statement:
--   Under the choice (18), $p=p_{\mathrm{sil}}+\eta$, $\gamma=\eta/4$, $\varepsilon=(\eta/16)^p$, the constant $a$ of Lemma 2.4 satisfies
--   $$\log a=O\bigl(\eta^{-1}\log(1/\eta)\bigr),\qquad 0<\eta\le1/10,$$
--   with an absolute implied constant: there is $C>0$ such that $\log a\le C\,\eta^{-1}\log(1/\eta)$ for every $\eta\in(0,1/10]$.
--
--   Balancing this growth of $a$ against the gain $\eta$ in the exponent is what produces the $\sqrt{\log\log n/\log n}$ loss in Theorem 1.1.
--
--   Differences from the source:
--   - encoding: log a = O(η⁻¹ log(1/η)), 0 < η ≤ 1/10 → ∃ C > 0, ∀ η ∈ (0, 1/10], log a ≤ C η⁻¹ log(1/η); reason: a ≥ 2, so log a > 0 and no absolute value is needed
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), (20), p. 15; proof §B.4, pp. 29–30

import Mathlib
import Definitions.Def_SilverRateLB_pSil
import Definitions.Def_SilverRateLB_aOf

namespace SilverRateLB

/-- **(20): growth of `a`.** Under the choice (18) (`p = p_sil + η`, `γ = η/4`, `ε = (η/16)^p`),
`log a = O(η⁻¹ log(1/η))` for `0 < η ≤ 1/10`, with an absolute implied constant.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, (20), p. 15 (proof §B.4, pp. 29–30).

**Formalization Note** The `O` is written with explicit quantifiers: one constant `C > 0` for every
`η ∈ (0, 1/10]`. No absolute value is needed: `a ≥ 2`, so `log a > 0`. -/
theorem eq_20_log_a :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 10 →
      Real.log (aOf ((η / 16) ^ (pSil + η)) (η / 4)) ≤ C * η⁻¹ * Real.log (1 / η) := by sorry

end SilverRateLB
