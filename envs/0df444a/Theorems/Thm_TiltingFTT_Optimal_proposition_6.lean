-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_proposition_6
-- name    : TiltingFTT.Optimal.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:51.042685+00:00
-- url     : https://prove2.me/theorems/3a7f83cd-83d0-472a-9084-9f6df3dc609e
-- title:
--   Proposition 6, p. 29 — starting from coexisting equilibria at τ = 0, the smallest tax τ* that rules out pooling is positive and, when τ* < τ_0, optimal
-- statement:
--   **Proposition 6 (Efficient FTT).** Assume the standing assumptions, specification (23) with value of information $v>0$, and that with no tax ($\tau=0$) the economy is in the region of Proposition 4 (ii) where a pooling equilibrium exists (with strict participation of the $L$-type) alongside a separating one. Let
--   $$\tau^*=\frac{\delta_I}{\delta_U}\frac{\bar F_L}{\bar F}-1,\qquad \tau_{FB}=\frac{\delta_I}{\delta_U}-1,$$
--   let $\tau_0$ be the welfare-indifference tax of the Pareto-optimal comparison, and assume $\tau^*<\tau_0$. Write $W_P$ for welfare in the Pareto-optimal pooling equilibrium ($T_P=1$) and $W_S(\tau)=W^*-(1-\beta)(\delta_I-\delta_U)(1-\bar T_L(\tau))F_L$ for welfare in the Pareto-optimal separating equilibrium. Then:
--
--   1. $0<\tau^*<\tau_{FB}$;
--   2. the value of information is high enough at $\tau=0$: $W_P<W_S(0)$;
--   3. for every $\tau\in[0,\tau^*]$ the Pareto-optimal pooling equilibrium $T_P=1$ exists, so such a tax does not change the equilibrium;
--   4. for every $\tau>\tau^*$ no pooling equilibrium exists (the tax tilts the economy);
--   5. for every $\tau\in(\tau^*,\tau_{FB}]$, $W_S(\tau)$ is the largest welfare attained by any separating equilibrium at $\tau$;
--   6. $W_S$ is strictly decreasing on $[0,\tau_{FB}]$;
--   7. $W_P<W_S(\tau^*)$;
--   8. for every $\tau\in(\tau^*,\tau_{FB}]$, $W_P<W_S(\tau)$ if and only if $\tau<\tau_0$;
--   9. for every $\tau>\tau_{FB}$ there is neither a separating nor a pooling equilibrium.
--
--   Read together: taxes up to $\tau^*$ leave welfare at $W_P$; every tax above $\tau^*$ moves the economy to a separating equilibrium whose best welfare $W_S(\tau)$ falls with $\tau$ and tends to $W_S(\tau^*)>W_P$ as $\tau\downarrow\tau^*$; above $\tau_{FB}$ trade breaks down. The welfare-maximizing tax is therefore the tilting threshold $\tau^*$, which is strictly positive.
--
--   **Formalization Note.** The paper's "$v>\bar v$" is a conclusion here (item 2), not a hypothesis: it follows from $\tau^*<\tau_0$, and $\bar v$ (Proposition 5) is not defined. The printed "$\tau^*\le\bar\tau$" is taken strictly, with $\bar\tau=\tau_0$ (the Pareto-optimal comparison): at $\tau^*=\tau_0$ the tilt yields no gain. "Optimal" is expressed through items 3–9 rather than as an attained maximum, because condition (22) is closed: the pooling equilibrium survives at $\tau=\tau^*$ itself, so $W_S(\tau^*)$ is a supremum approached from above $\tau^*$, not attained. The equilibrium-selection rule of p. 27 (the economy stays in the original equilibrium while it remains feasible) is the reading of items 3–4. The variant with $\bar\tau=\tau_1$ (least-trade separating comparison) is not formalized.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), Proposition 6, p. 29; proof in Appendix A, pp. 46–48

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem proposition_6 (P : Firm) (VH VL v : ℝ)
    (hS : Standing P) (h23 : Spec23 P VH VL v) (hv : 0 < v)
    (h0 : Coexist P 0) (hτ : tauStar P < tau0 P v) :
    0 < tauStar P ∧ tauStar P < tauFB P ∧
    poolWelfare P 0 1 < WS P 0 ∧
    (∀ τ, 0 ≤ τ → τ ≤ tauStar P → IsPoolingEq P τ 1) ∧
    (∀ τ, tauStar P < τ → ∀ TP, ¬ IsPoolingEq P τ TP) ∧
    (∀ τ, tauStar P < τ → τ ≤ tauFB P →
      IsGreatest {w | ∃ TH TL, IsSeparatingEq P τ TH TL ∧ w = sepWelfare P τ TH TL} (WS P τ)) ∧
    StrictAntiOn (WS P) (Set.Icc 0 (tauFB P)) ∧
    poolWelfare P 0 1 < WS P (tauStar P) ∧
    (∀ τ, tauStar P < τ → τ ≤ tauFB P →
      (poolWelfare P τ 1 < WS P τ ↔ τ < tau0 P v)) ∧
    (∀ τ, tauFB P < τ →
      (∀ TH TL, ¬ IsSeparatingEq P τ TH TL) ∧ ∀ TP, ¬ IsPoolingEq P τ TP) := by sorry

end TiltingFTT.Optimal
