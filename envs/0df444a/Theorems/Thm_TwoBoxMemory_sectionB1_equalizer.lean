-- Prove2me | Theorems.Thm_TwoBoxMemory_sectionB1_equalizer
-- name    : TwoBoxMemory.sectionB1_equalizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:51.019208+00:00
-- url     : https://prove2.me/theorems/9c96bb3a-1de2-42a3-aef9-907e2e94564f
-- title:
--   §B.1 — the greedy word $W$ is a minimax equalizer
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word.
--
--   Then
--
--   $$J_A(W)=\frac{C}{p}+D H_A,\qquad J_B(W)=\frac{D}{t}+C H_B,\qquad \frac{C}{p}+DH_A=\frac{D}{t}+CH_B,$$
--
--   $W$ is Bayes optimal for the positive prior $(\pi_A,\pi_B)$ of (B.2): $\pi_AJ_A(W)+\pi_BJ_B(W)\le\pi_AJ_A(w)+\pi_BJ_B(w)$ for every command word $w$, and consequently the unrestricted value is $V=C/p+DH_A$.
--
--   This identifies the value $V$ against which every excess $\Delta_M$ is measured, and the word whose prefixes finite controllers must imitate.
--
--   Differences from the source:
--   - encoding: W is Bayes optimal (among command laws) → Bayes risk of W at most that of every command word; reason: the Bayes risk of a law is the integral of the Bayes risks of its words, so the two statements are equivalent
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §B.1, p.21 (PDF 23); §6, after (6.1), p.8 (PDF 10)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- §B.1: the greedy word `W` is a minimax equalizer. At a non-tie positive saddle, with the saddle
cost `C = D v / u`, `J_A(W) = C/p + D H_A`, `J_B(W) = D/t + C H_B`, the two are equal, `W` is
Bayes optimal among all command words for the positive prior `(π_A, π_B)` of (B.2), and the
unrestricted value is `V = C/p + D H_A`.

**Formalization Note.** Bayes optimality is stated against every word `w : ℕ → Fin 2` in
`ℝ≥0∞`; the value is the infimum over all probability laws on words.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§B.1, p.21 (PDF 23); also §6, after (6.1), p.8 (PDF 10).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem sectionB1_equalizer (r s β D : ℝ) (hS : IsSaddle r s β D) :
    wordRisk r s (saddleCost r s β D) D 0 (greedyWord r s β) =
        ENNReal.ofReal ((saddleCost r s β D) / (1 - r) + D * HA r s β) ∧
      wordRisk r s (saddleCost r s β D) D 1 (greedyWord r s β) =
        ENNReal.ofReal (D / (1 - s) + (saddleCost r s β D) * HB r s β) ∧
      (saddleCost r s β D) / (1 - r) + D * HA r s β = D / (1 - s) + (saddleCost r s β D) * HB r s β ∧
      (∀ w : ℕ → Fin 2,
        ENNReal.ofReal (piA r s β D) * wordRisk r s (saddleCost r s β D) D 0 (greedyWord r s β) +
            ENNReal.ofReal (piB r s β D) * wordRisk r s (saddleCost r s β D) D 1 (greedyWord r s β) ≤
          ENNReal.ofReal (piA r s β D) * wordRisk r s (saddleCost r s β D) D 0 w +
            ENNReal.ofReal (piB r s β D) * wordRisk r s (saddleCost r s β D) D 1 w) ∧
      value r s (saddleCost r s β D) D = ENNReal.ofReal ((saddleCost r s β D) / (1 - r) + D * HA r s β) := by sorry

end TwoBoxMemory
