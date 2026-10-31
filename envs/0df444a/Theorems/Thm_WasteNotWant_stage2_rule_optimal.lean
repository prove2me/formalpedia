-- Prove2me | Theorems.Thm_WasteNotWant_stage2_rule_optimal
-- name    : WasteNotWant.stage2_rule_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:48.330773+00:00
-- url     : https://prove2.me/theorems/f8723215-ed0f-4b7d-b2df-833ad686d60c
-- title:
--   The stage-2 rule $q^Q_\delta$ is an optimal production decision
-- statement:
--   Fix stage-1 decisions $0\le q\le x$, a realized market size $y$ and $\delta>0$. In stage 2 the firm chooses a quantity $r\in[0,x-q]$, sells $\min\{D_f(y),q+r\}$ at price $p_f$, and pays $c+\delta$ per unit of $r$. Then $q^Q_\delta(x,q,y)\in[0,x-q]$ and
--   $$q^Q_\delta(x,q,y)\in\operatorname*{arg\,max}_{r\in[0,x-q]}\Bigl\{p_f\min\{D_f(y),q+r\}-(c+\delta)\,r\Bigr\}.$$
--
--   This is the backward-induction step that justifies substituting the rule into the expected profit (1).
--
--   Differences from the source:
--   - generalization: y a realization of Y, so y ∈ [a, b] → every real y; reason: the statement for all real y specializes to y ∈ [a, b]
--   - encoding: the optimal production decision is the rule → the rule is feasible and a maximizer; reason: at p_f = c + δ the maximizer is not unique, and the rule selects 0, as the printed text does
--   - reading: p_f > c + c_m → p_f > c + c_m together with p_f < 1, c_m > 0, c ≥ 0; reason: valuations are uniform on [0, 1] and the paper divides by 1 − p_f; c and c_m are unit costs; at c_m = 0 the optimal fabric level is not unique
--   - reading: given decisions (x, q) with q ≤ x → 0 ≤ q ≤ x; reason: the proof on p.44 states q ≥ 0
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), §3.1, p.10

import Mathlib
import Definitions.Def_WasteNotWant_Model

namespace WasteNotWant

/-- **The optimal stage-2 production rule.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), §3.1, p.10: given stage-1 decisions
`0 ≤ q ≤ x`, realized market size `y` and `δ > 0`, the rule `q^Q_δ(x, q, y)` is a feasible stage-2
production quantity and maximizes the stage-2 revenue net of production cost,
`r ↦ p_f min{D_f(y), q + r} - (c + δ) r`, over `r ∈ [0, x - q]`.

**Formalization Note.** The statement is optimality and not uniqueness: at `p_f = c + δ` several
quantities are optimal, and the rule selects `0`. It holds for every real `y`, which contains the
paper's `y ∈ [a, b]`. -/
theorem stage2_rule_optimal (P : Params) {δ x q : ℝ} (hδ : 0 < δ) (hq : 0 ≤ q) (hqx : q ≤ x)
    (y : ℝ) :
    stage2Rule P δ x q y ∈ Set.Icc 0 (x - q) ∧
      IsMaxOn (fun r : ℝ => P.pf * min (demand P y) (q + r) - (P.c + δ) * r)
        (Set.Icc 0 (x - q)) (stage2Rule P δ x q y) := by sorry

end WasteNotWant
