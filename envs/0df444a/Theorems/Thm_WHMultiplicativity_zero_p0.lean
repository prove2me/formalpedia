-- Prove2me | Theorems.Thm_WHMultiplicativity_zero_p0
-- name    : WHMultiplicativity.zero_p0
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:26:18.237256+00:00
-- url     : https://prove2.me/theorems/11ac8841-3382-4734-87af-5048a7aeba91
-- title:
--   §II, p.2: $\Delta(p,\Phi_m)$ has a single zero $p_0 \approx 4.7823$ on $(1,\infty)$, and $\Delta(\infty,\Phi_m) = \log(4/3) > 0$
-- statement:
--   Let $f(p) = \log\frac43 + \frac1p\log\big(\frac14 + 2^{1-2p}\big)$ be the closed form (13) of $\Delta(p,\Phi_m)$. Then:
--
--   1. there is a number $p_0$ with $4.7823 < p_0 < 4.7824$ and $f(p_0) = 0$;
--   2. $f(p) < 0$ for every $1 < p < p_0$;
--   3. $f(p) > 0$ for every $p > p_0$;
--   4. at $p = \infty$, $\Delta(\infty,\Phi_m) = \log(4/3) > 0$.
--
--   So additivity is violated for $p > p_0$ and for $p = \infty$, while the maximally entangled input gives no violation for $p$ close to $1$.
--
--   **Formalization Note** Items 1–3 are stated about the real function $f$; by eq. (13) it equals $\Delta(p,\Phi_m)$ for $p > 1$. Item 4 is stated about $\Delta$ itself (`delta 3 ⊤ (maxEnt 3)`).
--
--   Differences from the source:
--   - reading: the zero p0 is numerically determined as p0 = 4.7823 → p0 is a zero of log(4/3) + (1/p0) log(1/4 + 2^{1−2p0}) with 4.7823 < p0 < 4.7824; reason: the printed value is the four-decimal truncation of the zero 4.782311…; the bracket together with the equation pins p0, which is the stronger reading
--   - generalization: for p → 1 we have Δ(p, Φm) < 0 → f(p) < 0 for every p in (1, p0); reason: negativity on the whole interval implies negativity as p → 1; the paper's Fig. 1 shows it, and it is true (f(1) = 0, minimum about −0.203 near p ≈ 1.94)
--   - encoding: the zero and sign of Δ(p, Φm) → the zero and sign of the closed form f(p) of (13); reason: by eq. (13) (milestone eq_13) f(p) = Δ(p, Φm) for every p > 1
--   - encoding: log, base not specified → natural logarithm Real.log; reason: signs and zeros of Δ do not depend on the base; (13) holds in every base
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, §II, p.2 (sentences after eq. (13))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_maxEnt
import Definitions.Def_WHMultiplicativity_delta

open scoped ENNReal

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, §II, p.2 (after eq. (13)): "additivity is violated
for p > p0, where the zero p0 is numerically determined as p0 = 4.7823. In particular, we get
∆(∞, Φm) = log(4/3) > 0", and "for p → 1 we have ∆(p, Φm) < 0". With
`f(p) = log(4/3) + (1/p) log(1/4 + 2^{1−2p})`, the closed form (13) of `Δ(p, Φ_m)`:
there is `p₀` with `4.7823 < p₀ < 4.7824` and `f(p₀) = 0`, `f < 0` on `(1, p₀)`, `f > 0` on
`(p₀, ∞)`; and `Δ(∞, Φ_m) = log(4/3) > 0`.

**Formalization Note.** The printed `p₀ = 4.7823` is a four-decimal value of the zero
`4.78231…`; it is stated as the bracket `4.7823 < p₀ < 4.7824` together with `f(p₀) = 0`.
"For p → 1 we have Δ(p, Φ_m) < 0" is stated on the whole interval `(1, p₀)`. `Δ = delta 3`
(natural logarithm), `Φ_m = maxEnt 3`, `∞ = ⊤` (operator norm). -/
theorem zero_p0 :
    (∃ p0 : ℝ, 4.7823 < p0 ∧ p0 < 4.7824 ∧
        Real.log (4 / 3) + (1 / p0) * Real.log (1 / 4 + (2 : ℝ) ^ (1 - 2 * p0)) = 0 ∧
        (∀ p : ℝ, 1 < p → p < p0 →
          Real.log (4 / 3) + (1 / p) * Real.log (1 / 4 + (2 : ℝ) ^ (1 - 2 * p)) < 0) ∧
        (∀ p : ℝ, p0 < p →
          0 < Real.log (4 / 3) + (1 / p) * Real.log (1 / 4 + (2 : ℝ) ^ (1 - 2 * p)))) ∧
      delta 3 ⊤ (maxEnt 3) = Real.log (4 / 3) ∧ 0 < Real.log (4 / 3) := by sorry

end WHMultiplicativity
