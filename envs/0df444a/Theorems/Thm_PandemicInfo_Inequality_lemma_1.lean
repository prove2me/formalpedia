-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_lemma_1
-- name    : PandemicInfo.Inequality.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:02.46587+00:00
-- url     : https://prove2.me/theorems/c4e11f47-e1c1-44a2-b17b-bc2cc5bf6363
-- title:
--   Lemma 1, p. 18 (PDF 19) — $G_h,G_\ell,G_1,G_2$ strictly increasing; $G_h<G_1<G_\ell$ on $(4/5,1]$, $G_h<G_2<G_\ell$ on $[0,1/2)$
-- statement:
--   **Lemma 1.** The functions $G_h$, $G_\ell$, $G_1$ and $G_2$ of (23)–(25) are strictly increasing: $G_h$ and $G_\ell$ on each of $(-\infty,1/2)$ and $(1/2,\infty)$, $G_1$ on $(4/5,\infty)$ and $G_2$ on $(-\infty,1/2)$. Furthermore
--
--   $$G_h(\lambda)<G_1(\lambda)<G_\ell(\lambda)\quad(\lambda\in(4/5,1]),\qquad G_h(\lambda)<G_2(\lambda)<G_\ell(\lambda)\quad(\lambda\in[0,1/2)).$$
--
--   The lemma orders the regime boundaries (29)–(35) and makes the thresholds $\lambda_1,\dots,\lambda_4$ well defined.
--
--   **Formalization Note** $G_h$ and $G_\ell$ have a pole at $\lambda=1/2$, so "strictly increasing" is stated on each side separately, and $G_1$, $G_2$ on the domains (24)–(25) give them. Only $0<\omega_\ell<\omega_h$ from the standing assumptions (`Params.Standing`) is used.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 18 (PDF 19), Lemma 1

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Lemma 1, p. 18: `G_h`, `G_ℓ` (on each side of their pole `1/2`), `G_1` (on `(4/5, ∞)`) and `G_2`
(on `(−∞, 1/2)`) are strictly increasing; `G_h < G_1 < G_ℓ` on `(4/5, 1]` and
`G_h < G_2 < G_ℓ` on `[0, 1/2)`. -/
theorem lemma_1 (P : Params) (hS : P.Standing) :
    StrictMonoOn P.Gh (Set.Iio (1 / 2)) ∧ StrictMonoOn P.Gh (Set.Ioi (1 / 2)) ∧
    StrictMonoOn P.Gl (Set.Iio (1 / 2)) ∧ StrictMonoOn P.Gl (Set.Ioi (1 / 2)) ∧
    StrictMonoOn P.G1 (Set.Ioi (4 / 5)) ∧ StrictMonoOn P.G2 (Set.Iio (1 / 2)) ∧
    (∀ lam ∈ Set.Ioc (4 / 5 : ℝ) 1, P.Gh lam < P.G1 lam ∧ P.G1 lam < P.Gl lam) ∧
    (∀ lam ∈ Set.Ico (0 : ℝ) (1 / 2), P.G2 lam < P.Gl lam ∧ P.Gh lam < P.G2 lam) := by sorry

end PandemicInfo.Inequality
