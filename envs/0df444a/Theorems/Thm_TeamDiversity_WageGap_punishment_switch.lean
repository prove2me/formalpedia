-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_punishment_switch
-- name    : TeamDiversity.WageGap.punishment_switch
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:09.134318+00:00
-- url     : https://prove2.me/theorems/b9b03885-9715-454d-8866-cfd00d298a19
-- title:
--   Proof of Lemma 1, pp. 31–32 — (work, shirk) is self-enforcing iff δ ≤ δ^m, (shirk, shirk) iff δ ≥ δ^m; (shirk, shirk) always in diverse teams
-- statement:
--   Under the standing assumptions, fix $\delta \in [0,1]$. In the one-shot team game where an agent who exerts effort $e$ while the teammate exerts $e'$ earns $f_k(e+e')\,w - ce$:
--
--   1. at the specialized wage $w = \frac{(1-\delta)c}{f_s(2)-f_s(1)}$, the profile (work, shirk) is a Nash equilibrium of the specialized stage game if and only if $\delta \le \delta^m$;
--   2. at the specialized wage $w = \frac{c}{(1-\delta)(f_s(2)-f_s(1))+\delta(f_s(2)-f_s(0))}$, the profile (shirk, shirk) is a Nash equilibrium of the specialized stage game if and only if $\delta \ge \delta^m$;
--   3. at the diverse wage $w_d^* = \frac{c}{(1-\delta)(f_d(2)-f_d(1))+\delta(f_d(2)-f_d(0))}$, the profile (shirk, shirk) is a Nash equilibrium of the diverse stage game.
--
--   This is the content of the threshold $\delta^m$ in Lemma 1: it is the discount factor at which the self-enforcing punishment of a specialized team switches from (work, shirk) to (shirk, shirk), while a diverse team always uses (shirk, shirk).
--
--   **Formalization Note** A stage-game equilibrium is a pure Nash equilibrium over efforts in $\{0,1\}$, with success wage $w$ and failure payment $0$.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), proof of Lemma 1, pp. 31–32 (PDF 32–33)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Proof of Lemma 1, pp. 31–32: at the (work, shirk) wage `(1 − δ)c/(f_s(2) − f_s(1))` the
profile (work, shirk) is a stage-game equilibrium iff `δ ≤ δ^m`; at the (shirk, shirk) wage it is
(shirk, shirk) iff `δ ≥ δ^m`; and (shirk, shirk) is self-enforcing in diverse teams for every `δ`. -/
theorem punishment_switch (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) :
    ∀ δ ∈ Set.Icc (0 : ℝ) 1,
      (IsStageNE fs c ((1 - δ) * c / (fs.f2 - fs.f1)) 1 0 ↔ δ ≤ deltaM fs) ∧
      (IsStageNE fs c (c / ((1 - δ) * (fs.f2 - fs.f1) + δ * (fs.f2 - fs.f0))) 0 0 ↔
        deltaM fs ≤ δ) ∧
      IsStageNE fd c (c / ((1 - δ) * (fd.f2 - fd.f1) + δ * (fd.f2 - fd.f0))) 0 0 := by sorry

end TeamDiversity.WageGap
