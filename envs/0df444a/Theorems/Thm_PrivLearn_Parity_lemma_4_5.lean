-- Prove2me | Theorems.Thm_PrivLearn_Parity_lemma_4_5
-- name    : PrivLearn.Parity.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:11.714163+00:00
-- url     : https://prove2.me/theorems/1ac8519b-6fca-49d3-b0ba-1dd8c0174da0
-- title:
--   Lemma 4.5 — the amplified learner $\mathcal A^*$ is ε-differentially private (0 < ε ≤ 1/2)
-- statement:
--   For all constants $c, c' > 0$, all $d \ge 1$, $0 < \varepsilon \le 1/2$, $\alpha, \beta \in (0, 1/2)$ and every database size $n$, the algorithm $\mathcal A^*(\cdot, \varepsilon, \alpha, \beta)$ with constants $c, c'$ is $\varepsilon$-differentially private: for all neighboring databases $z, z'$ of $n$ labeled examples and every set $E$ of outputs,
--
--   $$
--   \Pr[\mathcal A^*(z,\varepsilon,\alpha,\beta) \in E] \le e^{\varepsilon} \Pr[\mathcal A^*(z',\varepsilon,\alpha,\beta) \in E].
--   $$
--
--   This is the privacy half of Theorem 4.4. It holds also when $n \le kn' + s$, where the output is the constant "insufficient samples".
--
--   **Formalization Note** The restriction $\varepsilon \le 1/2$ is inherited from Lemma 4.2, on which the paper's proof rests; the paper does not claim more than its proof gives for $\mathcal A$. Databases are arbitrary, labeled consistently or not.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 17, Lemma 4.5

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Amplified

namespace PrivLearn.Parity

/-- Lemma 4.5 (Privacy of A*), p. 17. For all constants `c, c′ > 0`, all `d ≥ 1`,
`0 < ε ≤ 1/2`, `α, β ∈ (0, 1/2)` and every database size `n`, the algorithm `A*(·, ε, α, β)` is
ε-differentially private. -/
theorem lemma_4_5 (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (d : ℕ) (hd : 1 ≤ d) (ε α β : ℝ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hα : 0 < α) (hα2 : α < 1 / 2) (hβ : 0 < β) (hβ2 : β < 1 / 2)
    (n : ℕ) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algAstar c c' d ε α β z) ε := by sorry

end PrivLearn.Parity
