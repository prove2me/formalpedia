-- Prove2me | Theorems.Thm_PrivLearn_Parity_lemma_4_1
-- name    : PrivLearn.Parity.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:13.09404+00:00
-- url     : https://prove2.me/theorems/9eb9204c-80e3-46d2-89cf-7fe30f4f356b
-- title:
--   Lemma 4.1 — the learner $\mathcal A$ outputs a hypothesis of error at most α with probability at least 1/4
-- statement:
--   Let $\mathcal X$ be a distribution on $\{0,1\}^d$ with $d \ge 1$, let $c_r \in$ PARITY, and let $z = (z_1,\dots,z_n)$ with $z_i = (x_i, c_r(x_i))$ and $x_1,\dots,x_n$ drawn i.i.d. from $\mathcal X$. Let $0 < \varepsilon \le 4$ and $0 < \alpha \le 1/2$. If
--
--   $$
--   n \ge \frac{8}{\varepsilon\alpha}\,(d \ln 2 + \ln 4),
--   $$
--
--   then
--
--   $$
--   \Pr\big[\mathcal A(z,\varepsilon) = c_{r'} \text{ for some } r' \text{ with } \mathrm{err}(c_{r'}) \le \alpha\big] \ge \tfrac14,
--   $$
--
--   the probability being over the examples and the coins of $\mathcal A$.
--
--   This is the utility of the basic private learner; the amplified learner $\mathcal A^*$ boosts the constant $1/4$ to $1 - \beta$.
--
--   **Formalization Note** The output $\bot$ is not a success. The paper assumes $\alpha \le 1/2$ in the proof ("the fact that $\alpha \le 1/2$"); $\varepsilon \le 4$ makes $p = \varepsilon/4$ a probability. $\ln$ is the natural logarithm, as printed. The statement is the printed one; the paper's own Chernoff step ($e^{-\varepsilon n/16}$) does not follow from Theorem A.1, which gives $e^{-\varepsilon n/32}$, but the printed conclusion still holds.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 14, Lemma 4.1

import Mathlib
import Definitions.Def_PrivLearn_Parity_Learner

open MeasureTheory

namespace PrivLearn.Parity

/-- Lemma 4.1 (Utility of A), p. 14. Let `𝒳` be a distribution on `{0,1}^d`, `c_r ∈ PARITY`, and
`z_i = (x_i, c_r(x_i))` with `x_1, …, x_n` i.i.d. from `𝒳`. If `n ≥ (8/(εα))(d ln 2 + ln 4)`, then
with probability at least `1/4` (over the examples and the coins of `A`) the algorithm `A(z, ε)`
outputs a hypothesis `c_{r'}` of error at most `α`. Here `0 < ε ≤ 4` (so that `p = ε/4` is a
probability) and `0 < α ≤ 1/2` (used in the paper's proof). -/
theorem lemma_4_1 {d n : ℕ} (hd : 1 ≤ d) (ε α : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (hα : 0 < α)
    (hα2 : α ≤ 1 / 2) (𝒳 : PMF (Fin d → ZMod 2)) (r : Fin d → ZMod 2)
    (hn : 8 / (ε * α) * (d * Real.log 2 + Real.log 4) ≤ n) :
    (1 / 4 : ENNReal) ≤
      samplePr 𝒳 r (fun z : Fin n → Example d => algA ε z)
        {o | ∃ r' : Fin d → ZMod 2, o = some r' ∧ err 𝒳 r (some r') ≤ α} := by sorry

end PrivLearn.Parity
