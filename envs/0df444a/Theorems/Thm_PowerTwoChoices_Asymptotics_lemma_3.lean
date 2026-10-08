-- Prove2me | Theorems.Thm_PowerTwoChoices_Asymptotics_lemma_3
-- name    : PowerTwoChoices.Asymptotics.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:45.126184+00:00
-- url     : https://prove2.me/theorems/f9396877-b6c8-436e-abc6-ffc72856a8ec
-- title:
--   Lemma 3: $\sum_{i\ge0}\lambda^{d^i}/\log\frac{1}{1-\lambda}\to1/\log d$ as $\lambda\to1^-$
-- statement:
--   Let $d\ge2$ be an integer and
--   $$F_d(\lambda)=\frac{\sum_{i=0}^{\infty}\lambda^{d^i}}{\log\frac{1}{1-\lambda}},\qquad 0<\lambda<1 .$$
--   Then
--   $$\lim_{\lambda\to1^-}F_d(\lambda)=\frac{1}{\log d}.$$
--
--   In words, the lacunary series $\sum_i\lambda^{d^i}$ grows like $\log_d\frac1{1-\lambda}$ as $\lambda$ approaches $1$. This is the analytic core of Theorem 4.
--
--   **Formalization Note.** Logarithms are natural (footnote 2, p. 1100). The limit is one-sided, taken along $\lambda<1$ (the filter `𝓝[<] 1`). The paper's statement does not repeat the standing assumption $d\ge2$ of §2.3; it is required, since $1/\log 1$ is undefined.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, Lemma 3

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

open Filter Topology

namespace PowerTwoChoices.Asymptotics

/-- Lemma 3 (Mitzenmacher 2001, p. 1099): for every integer `d ≥ 2`,
`F_d(λ) = (∑_{i ≥ 0} λ^{d^i}) / log(1/(1-λ)) → 1 / log d` as `λ → 1⁻`. -/
theorem lemma_3 (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (Fd d) (𝓝[<] (1 : ℝ)) (𝓝 (1 / Real.log (d : ℝ))) := by sorry

end PowerTwoChoices.Asymptotics
