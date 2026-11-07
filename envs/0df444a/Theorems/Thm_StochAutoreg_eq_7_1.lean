-- Prove2me | Theorems.Thm_StochAutoreg_eq_7_1
-- name    : StochAutoreg.eq_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:06.049208+00:00
-- url     : https://prove2.me/theorems/7bf0fc15-14a5-4015-b19e-79c770005187
-- title:
--   Eq. (7.1) — majority amplification: $F_J(t_G)=1/2+8\sqrt\varepsilon$, $F_J(t_H)=1/2+h_\varepsilon$, weak coins of KL $\le\varepsilon/100$
-- statement:
--   For odd $J$ let $F_J(t)=\Pr\{\mathrm{Bin}(J,1/2+t)>J/2\}$. Then $F_J'(0)=J\binom{J-1}{(J-1)/2}2^{-(J-1)}\sim\sqrt{2J/\pi}$, so an odd $J$ with $F_J'(0)\ge200$ exists. For such $J$ and all sufficiently small $\varepsilon>0$, the equation $\mathrm{KL}(1/2+h\|1/2)=\varepsilon$ has a unique solution $h_\varepsilon\in(0,1/4)$, and there are positive $t_G,t_H$ with
--
--   $$F_J(t_G)=\tfrac12+8\sqrt\varepsilon,\qquad F_J(t_H)=\tfrac12+h_\varepsilon,\qquad\mathrm{KL}(\tfrac12\pm t_G\|\tfrac12),\ \mathrm{KL}(\tfrac12\pm t_H\|\tfrac12)\le\frac\varepsilon{100}.$$
--
--   This turns a mean of size $\sqrt\varepsilon$ into many coins of negligible information each, the source of the separations.
--
--   Differences from the source:
--   - reading: "for all sufficiently small ε" → one threshold ε₁ depending only on J; reason: the paper fixes J first, and the theorem's ε₀ needs a threshold of this kind
--   - encoding: F_J'(0) ∼ √(2J/π) → the limit of the ratio along J = 2k+1; reason: the asymptotic is over odd J
--   - encoding: positive t_G, t_H → also t_G, t_H < 1/2, inside AmpData; reason: each weak coin must be a probability; the paper leaves this to "ε small"
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Eq. (7.1), pp.14–15

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_AmpData
import Definitions.Def_StochAutoreg_klBernE

namespace StochAutoreg

/-- **Majority amplification, Eq. (7.1).** `F_J'(0) = J binom(J-1, (J-1)/2) 2^{-(J-1)} ∼ √(2J/π)`, so an odd `J` with `F_J'(0) ≥ 200` exists. For
such `J` and all small `ε > 0`, `KL(1/2 + h‖1/2) = ε` has a unique solution `h_ε ∈ (0, 1/4)`, and there are positive `t_G, t_H` with
`F_J(t_G) = 1/2 + 8√ε`, `F_J(t_H) = 1/2 + h_ε`, `KL(1/2 ± t_G‖1/2), KL(1/2 ± t_H‖1/2) ≤ ε/100`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7, Eq. (7.1), pp.14–15.

**Formalization Note.** `∼` is the limit of the ratio along the odd integers `J = 2k+1`. -/
theorem eq_7_1 :
    (∀ J : ℕ, Odd J → deriv (majF J) 0 =
      (J : ℝ) * ((J - 1).choose ((J - 1) / 2) : ℝ) * (2 : ℝ)⁻¹ ^ (J - 1)) ∧
    Filter.Tendsto (fun k : ℕ => deriv (majF (2 * k + 1)) 0 /
      Real.sqrt (2 * (2 * (k : ℝ) + 1) / Real.pi)) Filter.atTop (nhds 1) ∧
    (∃ J : ℕ, Odd J ∧ 200 ≤ deriv (majF J) 0) ∧
    ∀ J : ℕ, Odd J → 200 ≤ deriv (majF J) 0 →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
        ∃ h tG tH : ℝ, AmpData J ε h tG tH ∧
          ∀ h' : ℝ, 0 < h' → h' < 1 / 4 →
            klBernE (1 / 2 + h') (1 / 2) = ENNReal.ofReal ε → h' = h := by sorry

end StochAutoreg
