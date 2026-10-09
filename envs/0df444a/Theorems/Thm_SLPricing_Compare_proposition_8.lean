-- Prove2me | Theorems.Thm_SLPricing_Compare_proposition_8
-- name    : SLPricing.Compare.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:43.636738+00:00
-- url     : https://prove2.me/theorems/cd08de47-9e13-426d-811d-8ac347deb9ec
-- title:
--   Proposition 8, p. 24 — with SL there is $T(\gamma) \in (0,1]$ such that responsive pricing earns strictly more than pre-announced pricing for all $\delta_c \le T(\gamma)$
-- statement:
--   In the presence of SL ($\gamma > 0$), fix $\sigma_p$ and $c$, and write $\pi^*_p(\delta_c)$ and $\pi^*_r(\delta_c)$ for the firm's optimal expected profits under pre-announced and responsive pricing when the consumers' discount factor is $\delta_c$. Then there exists a threshold $T(\gamma) \in (0,1]$ such that
--   $$\pi^*_p(\delta_c) \;<\; \pi^*_r(\delta_c) \qquad \text{for every } \delta_c \in [0, T(\gamma)] .$$
--
--   Without SL the comparison goes the other way (Proposition 7): commitment is weakly better. With SL, when consumers are sufficiently impatient, the firm prefers to keep the flexibility to react to the reviews.
--
--   **Formalization Note** Both sides are computed in the same model, with the same $\gamma, \sigma_p, c$ and the discount factor set to $\delta_c$; the given $\delta_c$ of the parameter record is ignored. $T > 0$ is the content of the statement. The proposition gives no "only if" direction, and none is stated.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 8, p. 24; proof in Appendix A, p. 34

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Proposition 8, p. 24: in the presence of SL there is a threshold `T(γ) ∈ (0, 1]` such that for
every consumer discount factor `δc ≤ T(γ)` the firm's optimal expected profit is strictly higher
under responsive pricing than under pre-announced pricing (all other parameters fixed). -/
theorem proposition_8 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ T ∈ Ioc (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) T,
      preValue (P.withδc d) < respValue (P.withδc d) := by sorry

end SLPricing.Compare
