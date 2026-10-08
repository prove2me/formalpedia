-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_tendsto_Q_two
-- name    : SamuelCahnProphet.IID.tendsto_Q_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:04.289977+00:00
-- url     : https://prove2.me/theorems/63886903-8497-4d06-b146-389a8d5355bd
-- title:
--   Proof of Theorem 2, p. 1215 — Q(b, c) → 2 as c → ∞ and b → 0
-- statement:
--   Let
--   $$
--   Q(b, c) = 1 + \frac{e^{-b} - e^{-b-c}}{1 - e^{-b-c}} - \frac{b(e^{-b} - e^{-b-c})^2}{c(1 - e^{-b-c})(1 - e^{-b})}.
--   $$
--   Then $Q(b, c) \to 2$ as $b \to 0^+$ and $c \to \infty$ jointly:
--   $$
--   \lim_{b \to 0^+,\ c \to \infty} Q(b, c) = 2 .
--   $$
--
--   Together with the preceding milestone, this shows that the ratio of the prophet's value to the best threshold value can be made arbitrarily close to $2$, which is the lower half of Theorem 2.
--
--   **Formalization Note.** The joint limit is taken along the product filter of $b \to 0$ from the right and $c \to \infty$. The paper's numerical illustration $Q(10^{-2}, 10^3) = 1.99$ is a rounded value and is not formalized.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2, last sentence ("as c → ∞ and b → 0, Q(b, c) → 2")

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem tendsto_Q_two :
    Tendsto (fun p : ℝ × ℝ => Q p.1 p.2) ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 2) := by sorry

end SamuelCahnProphet.IID
