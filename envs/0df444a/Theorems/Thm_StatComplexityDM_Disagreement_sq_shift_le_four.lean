-- Prove2me | Theorems.Thm_StatComplexityDM_Disagreement_sq_shift_le_four
-- name    : StatComplexityDM.Disagreement.sq_shift_le_four
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:22.566048+00:00
-- url     : https://prove2.me/theorems/af9de39c-f8d9-44c7-a692-43ee2802d691
-- title:
--   Theorem 6.2 (proof), p. 106 — E_{M∼µ}E_{M̃∼µ}[(f^M(π) − f^{M̃}(π))²] ≤ 4·E_{M∼µ}[(f^M(π) − f^{M̄}(π))²]
-- statement:
--   Let $\mu = \sum_i w_i \delta_{M_i}$ be a finitely supported prior over models with mean-reward functions $f^{M_i} : \Pi \to \mathbb{R}$, and let $f^{\overline{M}} : \Pi \to \mathbb{R}$ be the mean reward of a reference model $\overline{M}$. Then for every decision $\pi \in \Pi$,
--   $$
--   \mathbb{E}_{M\sim\mu}\, \mathbb{E}_{\widetilde{M}\sim\mu}\Bigl[\bigl(f^M(\pi) - f^{\widetilde{M}}(\pi)\bigr)^2\Bigr] \le 4\, \mathbb{E}_{M\sim\mu}\Bigl[\bigl(f^M(\pi) - f^{\overline{M}}(\pi)\bigr)^2\Bigr],
--   $$
--   where $M$ and $\widetilde{M}$ are independent draws from $\mu$.
--
--   This inequality lets the proof of Theorem 6.2 replace the decoupled error against a second draw from the prior by the square-loss error against the reference model.
--
--   **Formalization Note** The prior is a finite weighted family of mean-reward functions.
-- source:
--   arXiv:2112.13487v3, App. E.2.2, proof of Theorem 6.2, p. 106 ("Observe that for all π ∈ Π")

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

namespace StatComplexityDM.Disagreement

/-- Proof of Theorem 6.2, p. 106 (arXiv:2112.13487v3): for a finitely supported prior
`µ = Σ_i w i · δ_{M_i}` with mean rewards `fM i = f^{M_i}`, a reference mean reward `fbar = f^{M̄}`,
and every decision `π`,
`E_{M∼µ} E_{M̃∼µ}[(f^M(π) − f^{M̃}(π))²] ≤ 4 E_{M∼µ}[(f^M(π) − f^{M̄}(π))²]`. -/
theorem sq_shift_le_four {ι Act : Type*} [Fintype ι] (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fM : ι → Act → ℝ) (fbar : Act → ℝ) (π : Act) :
    ∑ i, w i * ∑ k, w k * (fM i π - fM k π) ^ 2 ≤ 4 * ∑ i, w i * (fM i π - fbar π) ^ 2 := by sorry

end StatComplexityDM.Disagreement
