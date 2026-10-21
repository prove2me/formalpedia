-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_proposition_2
-- name    : TiltingFTT.Optimal.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:35.190977+00:00
-- url     : https://prove2.me/theorems/73bbb22f-5718-430f-8c1d-f9b5cdeccc6a
-- title:
--   Proposition 2, p. 17 — a separating equilibrium exists iff δ_I ≥ (1+τ)δ_U; then T_H = 1 and T_L lies between the bounds (32)
-- statement:
--   Assume the standing assumptions of the model and fix a tax $\tau\ge 0$. Write $c=(1+\tau)\delta_U$.
--
--   1. A separating equilibrium exists if and only if the adjusted liquidity ratio is at least one: $$\frac{\delta_I}{\delta_U(1+\tau)}\ge 1.$$
--   2. If the ratio is strictly larger than one, then $(T_H,T_L)$ is a separating equilibrium if and only if $$T_H=1,\qquad \max\{0,\underline T_L\}\le T_L\le \bar T_L,\qquad T_L<1;$$ moreover $\underline T_L\le\bar T_L$ and $\underline T_L<1$; $\bar T_L\le 1$ under condition (17) $\frac{F_H-F_L}{F_H-F^L_H}\ge\frac{\delta_I}{\delta_U(1+\tau)}$, $\bar T_L<1$ when (17) is strict, and $\bar T_L>1$ when (17) fails (the "no-envy" case, in which $T_L$ can be arbitrarily close to $1$).
--   3. $\bar T_L$ is strictly decreasing in $\tau$ on $[0,\tau_{FB}]$ and $\underline T_L$ is strictly decreasing in $\tau$ on $[0,\tau_{FB})$, where $\tau_{FB}=\delta_I/\delta_U-1$.
--   4. Prices reveal the state: $P_L=\delta_UF_L<\delta_UF_H=P_H$.
--
--   This characterizes the informative equilibria of the trading game and identifies $T_H=1$, $T_L=\bar T_L$ as the Pareto-optimal separating outcome used in the welfare analysis.
--
--   **Formalization Note.** The paper's item (i) $T_H=1$ fails at the boundary $\delta_I=(1+\tau)\delta_U$, where every payoff vanishes and every $(t,0)$ with $t\in(0,1]$ is a separating equilibrium; the characterization is therefore stated for the strict inequality, while existence is stated for the closed one. The printed "$1>\bar T_L$ if (17)" is false at equality in (17) (then $\bar T_L=1$); the statement gives $\bar T_L\le 1$ under (17) and $\bar T_L<1$ under strict (17). Item (iii)'s optimal investment is built into the model (separating firm value $F_\omega$).
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), Proposition 2, p. 17, with (17), and its proof in Appendix A, (29)–(32), pp. 41–43

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem proposition_2 (P : Firm) (τ : ℝ) (hS : Standing P) (hτ : 0 ≤ τ) :
    ((∃ TH TL, IsSeparatingEq P τ TH TL) ↔ Cond15 P τ) ∧
    ((1 + τ) * P.δU < P.δI →
      (∀ TH TL, IsSeparatingEq P τ TH TL ↔
        TH = 1 ∧ max 0 (Tlow P τ) ≤ TL ∧ TL ≤ Tbar P τ ∧ TL < 1) ∧
      Tlow P τ ≤ Tbar P τ ∧ Tlow P τ < 1 ∧
      (Cond17 P τ → Tbar P τ ≤ 1) ∧
      (P.δI * (P.FH - P.FLH) < (1 + τ) * P.δU * (P.FH - P.FL) → Tbar P τ < 1) ∧
      (¬ Cond17 P τ → 1 < Tbar P τ)) ∧
    StrictAntiOn (Tbar P) (Set.Icc 0 (tauFB P)) ∧
    StrictAntiOn (Tlow P) (Set.Ico 0 (tauFB P)) ∧
    P.δU * P.FL < P.δU * P.FH := by sorry

end TiltingFTT.Optimal
