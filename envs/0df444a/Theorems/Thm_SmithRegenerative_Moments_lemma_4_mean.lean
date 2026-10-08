-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_lemma_4_mean
-- name    : SmithRegenerative.Moments.lemma_4_mean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:16.322278+00:00
-- url     : https://prove2.me/theorems/781f9980-52bf-4e72-80f4-2bb1f0d38ffd
-- title:
--   Lemma 4, (5·2·3) — mean of the overshoot reward
-- statement:
--   Let $Y_t=\sum_{i=1}^{n_t+1}y_i$ for a cumulative process. If the first cycle length and reward are integrable, with means $\mu_1$ and $\kappa_1$, then $Y_t$ is integrable for every $t\geq0$ and
--
--   $$
--   \mathbb E Y_t=\frac{\kappa_1}{\mu_1}t+o(t)\qquad(t\to\infty).
--   $$
--
--   This is the renewal-reward mean estimate used in the mean part of Theorem 8.
--
--   **Formalization Note** The printed exact identity (5·2·2) is off by one for the paper's definitions of $n_t$ and $Y_t$. The asymptotic statement (5·2·3) remains valid.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 23, Lemma 4, (5·2·3)

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_CumulativeProcess

namespace SmithRegenerative.Moments

open MeasureTheory Filter

/-- Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), p. 23, Lemma 4, (5·2·3).
Formalization Note: `Y_t` retains the upper index `n_t+1` of (5·2·1).
The printed intermediate identity (5·2·2) is off by one for this convention,
but the stated `o(t)` conclusion is unaffected. Integrability of `Y_t` is
made explicit instead of using Lean's zero default for a divergent integral. -/
theorem lemma_4_mean {Ω : Type*} [MeasurableSpace Ω]
    (C : CumulativeProcess Ω)
    (hμ : Integrable (C.renewal.cycleLength 1) C.renewal.P)
    (hκ : Integrable (cycleReward C.renewal C.w 1) C.renewal.P) :
    (∀ t : ℝ, 0 ≤ t → Integrable (C.overshootReward t) C.renewal.P) ∧
    (fun t : ℝ =>
      (∫ ω, C.overshootReward t ω ∂C.renewal.P) -
        C.meanReward / C.meanLength * t) =o[atTop] (fun t : ℝ => t) := by sorry

end SmithRegenerative.Moments
