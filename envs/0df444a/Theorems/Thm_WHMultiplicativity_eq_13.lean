-- Prove2me | Theorems.Thm_WHMultiplicativity_eq_13
-- name    : WHMultiplicativity.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:26:47.825824+00:00
-- url     : https://prove2.me/theorems/ccedcc9e-c6e5-45f5-a3e8-266623157e48
-- title:
--   Eq. (13): $\Delta(p,\Phi_m) = \log\frac43 + \frac1p\log\big(\frac14 + 2^{1-2p}\big)$
-- statement:
--   Let $d = 3$, let $S$ be the Werner–Holevo channel, $\Phi_m$ the maximally entangled vector in $\mathbb C^3\otimes\mathbb C^3$, and $\Delta(p,\Phi) = \log\|S\otimes S(|\Phi\rangle\langle\Phi|)\|_p - 2\log\nu_p(S)$ as in eq. (12). For every real $p > 1$,
--
--   $$
--   \Delta(p,\Phi_m) = \log\frac43 + \frac1p\log\Big(\frac14 + 2^{1-2p}\Big).
--   $$
--
--   A positive value of $\Delta(p,\Phi_m)$ shows $\nu_p(S\otimes S) > \nu_p(S)^2$.
--
--   Differences from the source:
--   - encoding: log, base not specified → natural logarithm Real.log; reason: signs and zeros of Δ do not depend on the base; (13) holds in every base
--   - encoding: Δ(p, Φm) for the paper's 1 < p < ∞ → delta 3 (ENNReal.ofReal p) (maxEnt 3) for real p > 1; reason: Δ of (12) with d = 3, the norm exponent entering as an extended real
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eqs. (12)–(13), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_maxEnt
import Definitions.Def_WHMultiplicativity_delta

open scoped ENNReal

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eqs. (12)–(13), p.2: inserting the maximally
entangled vector into `Δ(p, Φ) = log ‖S ⊗ S(|Φ⟩⟨Φ|)‖_p − 2 log ν_p(S)` gives, for `d = 3`,
`Δ(p, Φ_m) = log(4/3) + (1/p) log(1/4 + 2^{1−2p})`.

**Formalization Note.** `Δ = delta 3` (natural logarithm), `Φ_m = maxEnt 3`. A real `p` with
`1 < p` (the paper's range) enters as `ENNReal.ofReal p`. The paper's "log 4/3" is
`log(4/3)`. -/
theorem eq_13 (p : ℝ) (hp : 1 < p) :
    delta 3 (ENNReal.ofReal p) (maxEnt 3) =
      Real.log (4 / 3) + (1 / p) * Real.log (1 / 4 + (2 : ℝ) ^ (1 - 2 * p)) := by sorry

end WHMultiplicativity
