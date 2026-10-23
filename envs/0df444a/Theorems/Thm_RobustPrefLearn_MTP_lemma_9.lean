-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_9
-- name    : RobustPrefLearn.MTP.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:10.00112+00:00
-- url     : https://prove2.me/theorems/342b06e7-5800-4a93-b827-7114e667a4e1
-- title:
--   Lemma 9, p. 63 — u* = l*
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. The primal and dual values coincide:
--   $$u^*=\frac1{\lambda^*_2+\dots+\lambda^*_K}=\frac1{\mu_2+\dots+\mu_K}=l^*.$$
--
--   With Lemmas 7 and 8 it shows by weak duality that $\lambda^{\mathrm{OA}}_*$ solves (LP-P).
--
--   **Formalization Note** The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 63, Lemma 9

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Lemma 9, p. 63. `u* = l*`, i.e. `1/(λ*_2 + ⋯ + λ*_K) = 1/(µ_2 + ⋯ + µ_K)`. -/
theorem lemma_9 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    uStar K p = lStar K p := by sorry

end RobustPrefLearn.MTP
