-- Prove2me | Theorems.Thm_TwoBoxMemory_sectionB3_departure_excess
-- name    : TwoBoxMemory.sectionB3_departure_excess
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:06.037278+00:00
-- url     : https://prove2.me/theorems/7a225722-6d47-4983-91bd-01cbc6b8ab16
-- title:
--   §B.3 — first departure from $W$ costs at least $d_h$
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word. Let $V$ be the unrestricted value and $d_h$ the first-departure margin. For every $h\ge0$:
--
--   1. every command word $w$ that differs from $W$ at some position $k<h$ has Bayes cost
--   $$\pi_AJ_A(w)+\pi_BJ_B(w)\ \ge\ V+d_h;$$
--   2. every probability law $P$ on words satisfies $\max(J_A(P),J_B(P))\ge V+\eta\,d_h$, where $\eta=P(\text{the length-}h\text{ prefix differs from }W_0\cdots W_{h-1})$;
--   3. every controller, with any number of labels, has worst risk at least $V+\bigl(1-P(W_0\cdots W_{h-1})\bigr)d_h$, where $P(W_0\cdots W_{h-1})$ is its cylinder probability of the length-$h$ prefix of $W$.
--
--   This turns a small excess into a high probability of following $W$ for $h$ steps, which the rank bound then exploits.
--
--   Differences from the source:
--   - encoding: a word that first differs from W within its first h symbols → a word with w_k ≠ W_k for some k < h; reason: same set of words
--   - encoding: a controller whose length-h prefix differs with probability η → η = 1 − cylinder probability of W_0⋯W_{h−1}; reason: the cylinder probabilities of the length-h words sum to 1
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §B.3, around (B.8), p.22 (PDF 24); (6.2), p.9 (PDF 11)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- §B.3: the first-departure excess. At a non-tie positive saddle (cost `C = D v / u`), for every
`h`:
1. every command word that differs from `W` at some position `< h` has Bayes cost
   `π_A J_A + π_B J_B ≥ V + d_h`;
2. every probability law `P` on words has `max(J_A(P), J_B(P)) ≥ V + η d_h`, where `η` is the
   probability that the length-`h` prefix differs from that of `W`;
3. every controller has worst risk `≥ V + (1 − P(W_0 ⋯ W_{h−1})) d_h`, its cylinder probability
   of the length-`h` prefix of `W` being `P(W_0 ⋯ W_{h−1})`.

**Formalization Note.** Risks are in `ℝ≥0∞`. Controllers have any number of labels.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§B.3, before (B.8)–after (B.8), p.22 (PDF 24); (6.2), p.9 (PDF 11).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem sectionB3_departure_excess (r s β D : ℝ) (hS : IsSaddle r s β D) (h : ℕ) :
    (∀ w : ℕ → Fin 2, (∃ k < h, w k ≠ greedyWord r s β k) →
      value r s (saddleCost r s β D) D + ENNReal.ofReal (departureMargin r s β D h) ≤
        ENNReal.ofReal (piA r s β D) * wordRisk r s (saddleCost r s β D) D 0 w +
          ENNReal.ofReal (piB r s β D) * wordRisk r s (saddleCost r s β D) D 1 w) ∧
    (∀ P : Measure (ℕ → Fin 2), IsProbabilityMeasure P →
      value r s (saddleCost r s β D) D +
          P {w | ∃ k < h, w k ≠ greedyWord r s β k} * ENNReal.ofReal (departureMargin r s β D h) ≤
        max (lawRisk r s (saddleCost r s β D) D 0 P) (lawRisk r s (saddleCost r s β D) D 1 P)) ∧
    (∀ (m : ℕ) (κ : Controller m),
      value r s (saddleCost r s β D) D +
          ENNReal.ofReal ((1 - cylProb κ (wordPrefix (greedyWord r s β) h)) * departureMargin r s β D h) ≤
        worstRisk r s (saddleCost r s β D) D κ) := by sorry

end TwoBoxMemory
