-- Prove2me | Theorems.Thm_StatComplexityDM_Estimation_affinity_eq_one_sub_half_hellinger
-- name    : StatComplexityDM.Estimation.affinity_eq_one_sub_half_hellinger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:25.117445+00:00
-- url     : https://prove2.me/theorems/a5a8b0d9-3ff3-4626-8cae-f884bd858041
-- title:
--   Proof of Lemma A.14, p. 79 — affinity equals one minus half squared Hellinger distance
-- statement:
--   Let $P$ and $Q$ be probability vectors on a finite set $Y$. Their Hellinger affinity satisfies
--   $$
--   \sum_{y\in Y}\sqrt{P(y)Q(y)}=1-\tfrac12 D_{\mathrm H}^2(P,Q).
--   $$
--   The expectation under $P$ of $\sqrt{Q(y)/P(y)}$, summed over $\{y:P(y)>0\}$, has the same value.
--
--   This is the normalization identity in the conditional exponential-moment calculation for Lemma A.14.
--
--   **Formalization Note** $D_{\mathrm H}^2(P,Q)=\sum_y(\sqrt{P(y)}-\sqrt{Q(y)})^2$ has no factor of $1/2$. The support restriction keeps the ratio's denominator positive.
-- source:
--   arXiv:2112.13487v3, Appendix A.3.5, proof of Lemma A.14, p. 79, affinity identity following (103)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_Estimation_Sequential

namespace StatComplexityDM.Estimation

open FoundationsRL.GeneralDM Classical

/-- The affinity identity used in the proof of Lemma A.14, p. 79. -/
theorem affinity_eq_one_sub_half_hellinger {Y : Type*} [Fintype Y]
    (P Q : Y → ℝ) (hP : StatComplexityDM.LowerBound.IsDist P) (hQ : StatComplexityDM.LowerBound.IsDist Q) :
    (∑ y, Real.sqrt (P y * Q y)) = 1 - hellingerSq P Q / 2 ∧
    (∑ y, if 0 < P y then P y * Real.sqrt (Q y / P y) else 0) =
      1 - hellingerSq P Q / 2 := by sorry

end StatComplexityDM.Estimation
