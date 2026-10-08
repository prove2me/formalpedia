-- Prove2me | Theorems.Thm_PrivLearn_Parity_lemma_4_2
-- name    : PrivLearn.Parity.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:41.056484+00:00
-- url     : https://prove2.me/theorems/84a097c8-43e9-4a90-8a96-5ee04e6d11b7
-- title:
--   Lemma 4.2 — the learner $\mathcal A$ is ε-differentially private (0 < ε ≤ 1/2)
-- statement:
--   Let $d, n \in \mathbb N$ and $0 < \varepsilon \le 1/2$. The algorithm $\mathcal A(\cdot, \varepsilon)$, on databases of $n$ labeled examples in $\{0,1\}^d \times \{0,1\}$, is $\varepsilon$-differentially private: for all neighboring databases $z, z'$ and every set $E$ of outputs,
--
--   $$
--   \Pr[\mathcal A(z,\varepsilon) \in E] \le e^{\varepsilon} \Pr[\mathcal A(z',\varepsilon) \in E].
--   $$
--
--   Privacy holds for every database, including databases no parity function labels consistently.
--
--   **Formalization Note** The paper states the lemma for all $\varepsilon$; its proof uses $\varepsilon \le 1/2$ ("since $p = \varepsilon/4$ and $\varepsilon \le 1/2$"), and the step $2p/(1-p) + 1 \le \varepsilon + 1$ fails for larger $\varepsilon$. We state it for $0 < \varepsilon \le 1/2$. The paper checks the pointwise inequalities (2) and (3); on the finite output space they are equivalent to the set form stated here.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 15, Lemma 4.2

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Learner

namespace PrivLearn.Parity

/-- Lemma 4.2 (Privacy of A), p. 15. For `0 < ε ≤ 1/2` (the range the paper's proof uses) the
algorithm `A(·, ε)` is ε-differentially private, on databases of any size `n` over
`{0,1}^d × {0,1}`, labeled consistently or not. -/
theorem lemma_4_2 (d n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Example d => algA ε z) ε := by sorry

end PrivLearn.Parity
