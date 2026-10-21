-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_proposition_3
-- name    : TiltingFTT.Optimal.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:43.466682+00:00
-- url     : https://prove2.me/theorems/f44accd8-1104-48c1-b72f-7f79e4086681
-- title:
--   Proposition 3, pp. 20–21 — pooling equilibria exist iff (22); then T̲_P ≤ T_P ≤ 1 with T̲_P decreasing in τ
-- statement:
--   Assume the standing assumptions and fix $\tau\ge0$.
--
--   1. A pooling equilibrium exists if and only if condition (22) holds:
--   $$\frac{F_H-\bar F}{F_H-\bar F_H}\ \ge\ \frac{\delta_I}{\delta_U(1+\tau)}\ \ge\ \frac{\bar F}{\bar F_L}.$$
--   2. Under (22), the lower bound $\underline T_P=\frac{(\delta_I-(1+\tau)\delta_U)F_H}{\delta_I\bar F_H-(1+\tau)\delta_U\bar F}$ is positive and $T_P$ is a pooling equilibrium trade if and only if $\underline T_P\le T_P\le 1$.
--   3. $\underline T_P$ is strictly decreasing in $\tau$ on $[0,\tau_{FB}]$.
--
--   The pooling equilibria are the liquid but uninformative outcomes of the model; the Pareto-optimal one has $T_P=1$.
--
--   **Formalization Note.** Both inequalities of (22) are cross-multiplied; when $F_H=\bar F_H$ the paper reads the left fraction as arbitrarily large, which the cross-multiplied form reproduces. Items (ii) (price $P_P=\delta_U\bar F$) and (iii) (firm value $\bar F_\omega$) are built into the definition of a pooling equilibrium and are not restated. The definition excludes no-trade, $T_P>0$, as the paper does on p. 22.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), Proposition 3, pp. 20–21, with (22), and its proof in Appendix A, (33) and T̲_P, pp. 43–45

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem proposition_3 (P : Firm) (τ : ℝ) (hS : Standing P) (hτ : 0 ≤ τ) :
    ((∃ TP, IsPoolingEq P τ TP) ↔ Cond22 P τ) ∧
    (Cond22 P τ →
      0 < TlowP P τ ∧ ∀ TP, IsPoolingEq P τ TP ↔ TlowP P τ ≤ TP ∧ TP ≤ 1) ∧
    StrictAntiOn (TlowP P) (Set.Icc 0 (tauFB P)) := by sorry

end TiltingFTT.Optimal
