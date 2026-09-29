-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_decoding_step
-- name    : SetCoverThreshold.MaxCover.decoding_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:06:24.658976+00:00
-- url     : https://prove2.me/theorems/cdd1c2fc-df0e-4aa7-bca5-ad24d5fada6c
-- title:
--   Decoding step — from ε/3 good r to a strategy weakly accepting with probability (ε/3)(ε/3k)^2
-- statement:
--   Let $\varepsilon>0$, let $k,\ell$, a code, a 3CNF-5 formula $\varphi$ and a collection $\mathcal C$ of sets of the §5 instance be given, and suppose at least an $\varepsilon/3$-fraction of the random strings are good for $\mathcal C$ (i.e. $w_r\le 3k/\varepsilon$ and two sets of $\mathcal C$ from different provers induce the same partition label on $r$). Then some deterministic strategy of the $k$ provers makes the verifier weakly accept with probability at least
--   $$\frac{\varepsilon}{3}\Big(\frac{\varepsilon}{3k}\Big)^2 .$$
--
--   This turns a good covering into a good strategy for the $k$-prover proof system; combined with the soundness bound $k^2 2^{-c\ell}$ of Lemma 2.3.1 it yields a contradiction for large $\ell$.
--
--   **Formalization Note** The paper writes the bound as "$\epsilon/3(\epsilon/3k)^2$", read here as $(\varepsilon/3)\cdot(\varepsilon/(3k))^2$, which is what the computation of Proposition 4.3 gives. Hypothesis and conclusion are stated as counts over the $R=(3M)^\ell$ random strings.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 649, proof of Theorem 5.3 (after Proposition 5.4)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

/-- **Decoding step** (Feige 1998, p. 649, proof of Theorem 5.3): if at least an `ε/3`-fraction
of the random strings are good for a collection `C` of sets of the §5 instance, then some
strategy of the `k` provers makes the verifier weakly accept with probability at least
`(ε/3) · (ε/(3k))^2`. -/
theorem decoding_step (ε : ℝ) (hε : 0 < ε) (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool)
    (φ : Formula5) (C : Finset (SetIdx φ code))
    (hgood : ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ)) :
    ∃ strat : Fin k → Strategy φ ℓ,
      ε / 3 * (ε / (3 * k)) ^ 2 * (Fintype.card (RandString φ ℓ) : ℝ) ≤
        (weakAcceptCount φ code strat : ℝ) := by sorry

end SetCoverThreshold.MaxCover
