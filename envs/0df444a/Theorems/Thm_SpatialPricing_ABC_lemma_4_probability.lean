-- Prove2me | Theorems.Thm_SpatialPricing_ABC_lemma_4_probability
-- name    : SpatialPricing.ABC.lemma_4_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:14.387673+00:00
-- url     : https://prove2.me/theorems/a4e2485b-1be8-4dd0-b958-252f45052eba
-- title:
--   Lemma 4 (probability), p. 25 — the ABC good event has probability at least 1−2N²/(bTⁿ)
-- statement:
--   Under the standing spatial pricing assumptions, fix $n\ge1$ and the ABC parameters from Theorem 3. Suppose $\mathrm{DCP}(n,\zeta_n)$ is feasible and $2\eta_n/b_n<1$, where $\eta_n=(\epsilon_n\underline\tau^n-1)/4$. Let $\mathcal A$ be the event on which every within-batch partial sum of realized demand minus the posted ABC rate has magnitude less than $\eta_n$. Then
--
--   $$\Pr_{ABC}(\mathcal A)\ge1-\frac{2N^2}{b_nT^n}.$$
--
--   This supplies the probability estimate used to control the revenue contribution of paths outside $\mathcal A$.
--
--   **Formalization Note** Feasibility replaces the $\bar\zeta>\zeta$ clause of C2. The manuscript's printed proof bounds adaptive rates by a variance proxy for the deterministic DCP baseline; that step needs a separate justification and is flagged in the moderation notes.
-- source:
--   Chen, Lei, Jasin, accepted manuscript, LBS Research Online eprint 2845, PDF sha256 7310a8a1…480a, pp. 24–25, C2, event A, Lemma 4 (PDF 25–26)

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting
import Definitions.Def_SpatialPricing_ABC_Control

namespace SpatialPricing.ABC

/-- Lemma 4, p. 25: probability of the batchwise good event. -/
theorem lemma_4_probability (P : Instance) (Ψ3 : ℝ) (hP : P.Standing Ψ3)
    (n : ℕ) (hn : 1 ≤ n)
    (hfeas : ∃ x, (P.scale n).DCPFeasible (P.zetaN n) x)
    (hC2 : 2 * P.etaN n / P.bN n < 1) :
    1 - 2 * (P.N : ℝ) ^ 2 / (P.bN n * P.TN n) ≤
      (P.scale n).prob
        ((P.scale n).abcRate (P.epsN n) (P.zetaN n) (P.bN n))
        ((P.scale n).inA (P.epsN n) (P.zetaN n) (P.bN n) (P.etaN n)) := by sorry

end SpatialPricing.ABC
