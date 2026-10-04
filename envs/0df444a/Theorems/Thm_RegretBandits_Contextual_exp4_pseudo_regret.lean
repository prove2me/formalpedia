-- Prove2me | Theorems.Thm_RegretBandits_Contextual_exp4_pseudo_regret
-- name    : RegretBandits.Contextual.exp4_pseudo_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:50:24.724681+00:00
-- url     : https://prove2.me/theorems/7dd71bab-08bc-44f0-a22e-86d0a09d5e0d
-- title:
--   Theorem 4.2 — pseudo-regret of Exp4 (corrected constants)
-- statement:
--   Let $K \ge 2$ arms and $N \ge 1$ experts. At each round each expert $j$ recommends a distribution $\xi^j_t$ over arms, which may depend on the forecaster's past plays, and an adaptive adversary assigns losses $\ell_{i,t} \in [0,1]$. Let $I_t$ be the arms played by Exp4 without mixing. Then for every expert $k$:
--
--   1. with the constant learning rate $\eta_t = \sqrt{2\ln N/(nK)}$,
--   $$\mathbb E\left[\sum_{t=1}^n \ell_{I_t,t} - \sum_{t=1}^n \mathbb E_{i\sim\xi^k_t}\ell_{i,t}\right] \le \sqrt{2nK\ln N};$$
--   2. with the anytime learning rate $\eta_t = \sqrt{\ln N/(tK)}$, for every $n$,
--   $$\mathbb E\left[\sum_{t=1}^n \ell_{I_t,t} - \sum_{t=1}^n \mathbb E_{i\sim\xi^k_t}\ell_{i,t}\right] \le 2\sqrt{nK\ln N}.$$
--
--   Thus the contextual pseudo-regret $\overline R^{\mathrm{ctx}}_n$ grows only logarithmically in the number of experts.
--
--   **Formalization Note** Corrected misprint: the book prints (4.1) as $\overline R^{\mathrm{ctx}}_n \le \sqrt{2nN\ln K}$ and (4.2) as $2\sqrt{nN\ln K}$. Its proof (p. 48) ends with $\overline R^{\mathrm{ctx}}_n \le \frac{\ln N}{\eta_n} + \frac K2 \sum_{t=1}^n \eta_t$, which with the printed learning rates gives $\sqrt{2nK\ln N}$ and $2\sqrt{nK\ln N}$; the text before the theorem also announces order $\sqrt{nK\ln N}$. The Lean statement states the proof's bounds. The maximum over experts is written as "for every $k$". Rounds are 0-based in Lean; the anytime rate is `fun t => √(ln N/(tK))`, whose value at Lean index $0$ multiplies the zero vector and is never effective.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 46, Theorem 4.2, Eqs. (4.1)-(4.2); proof p. 47-48

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol
import Definitions.Def_RegretBandits_Contextual_Exp4

namespace RegretBandits.Contextual

/-- Theorem 4.2, corrected (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 46; the book prints
`√(2nN ln K)` and `2√(nN ln K)`, its proof on p. 48 gives the bounds below). Exp4 without mixing,
with `K ≥ 2` arms, `N ≥ 1` experts whose advice may depend on the forecaster's past plays, and an
adaptive adversary with losses in `[0,1]`, satisfies for every expert `k`:
(4.1) with `η_t = √(2 ln N/(nK))`, `E[∑_t ℓ_{I_t,t} - ∑_t E_{i∼ξ^k_t} ℓ_{i,t}] ≤ √(2 n K ln N)`;
(4.2) with `η_t = √(ln N/(tK))`, the same pseudo-regret is `≤ 2 √(n K ln N)` for every `n`. -/
theorem exp4_pseudo_regret {K N : ℕ} (hK : 2 ≤ K) (hN : 1 ≤ N)
    (ℓ : AdaptiveLosses K) (hℓ : ∀ t h i, 0 ≤ ℓ t h i ∧ ℓ t h i ≤ 1)
    (ξ : AdaptiveAdvice K N) (hξ : ∀ t h j, IsProbVec (ξ t h j)) :
    (∀ (n : ℕ) (k : Fin N),
      pathExpect (exp4Rule (fun _ => Real.sqrt (2 * Real.log N / (n * K))) ℓ ξ) n
          (fun ω => ∑ t : Fin n,
            (ℓ t (playPrefix ω t) (ω t) -
              ∑ i, ξ t (playPrefix ω t) k i * ℓ t (playPrefix ω t) i)) ≤
        Real.sqrt (2 * n * K * Real.log N)) ∧
    (∀ (n : ℕ) (k : Fin N),
      pathExpect (exp4Rule (fun t => Real.sqrt (Real.log N / (t * K))) ℓ ξ) n
          (fun ω => ∑ t : Fin n,
            (ℓ t (playPrefix ω t) (ω t) -
              ∑ i, ξ t (playPrefix ω t) k i * ℓ t (playPrefix ω t) i)) ≤
        2 * Real.sqrt (n * K * Real.log N)) := by sorry

end RegretBandits.Contextual
