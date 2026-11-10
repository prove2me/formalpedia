-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_A_11
-- name    : PrivGaussMS.lemma_A_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:15.881389+00:00
-- url     : https://prove2.me/theorems/168c11ee-48e5-44e8-b5a7-50822ce999f7
-- title:
--   Lemma A.11 — density of selected frame rows (4)
-- statement:
--   Let $r,p\ge1$ and $N\ge r+p$. The first $r$ rows $Z$ of a uniform $N\times p$ frame have Lebesgue density
--   $$c_{N,r,p}\det(I_p-Z^TZ)^{(N-r-p-1)/2}\mathbf 1\{I_p-Z^TZ\succ0\},\qquad c_{N,r,p}=\pi^{-rp/2}\prod_{j=1}^p\frac{\Gamma((N-j+1)/2)}{\Gamma((N-r-j+1)/2)}.$$
--   This includes $r<p$.
--
--   It is the source of every frame-block density in the construction.
--
--   Differences from the source:
--   - encoding: uniform frame → the law of the Gaussian polar factor G(GᵀG)^{−1/2}; reason: the paper's own construction of the uniform frame (p.28)
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.11, p.29, eq. (4)

import Mathlib
import Definitions.Def_PrivGaussMS_Frames
import Definitions.Def_PrivGaussMS_CandidateDensity

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-- **Lemma A.11** (Density of selected frame rows), Moayedi, Yassaee, Ebrahimi, *Optimal Private
Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), p.29, eq. (4).

For `r, p ≥ 1` and `N ≥ r + p`, the first `r` rows of a uniform `N × p` frame have Lebesgue
density `c_{N,r,p} det(I_p − ZᵀZ)^{(N−r−p−1)/2} 1{I_p − ZᵀZ ≻ 0}`, including `r < p`.

**Formalization Note.** `frameRowDensity` and `cFrame` are (4); the uniform frame is the
Gaussian polar factor (`Def_PrivGaussMS_Frames`); Lebesgue measure on `ℝ^{r×p}` is the entrywise
product. -/
theorem lemma_A_11 (N r p : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p) (hN : r + p ≤ N) :
    (uniformFrame N p).map (firstRows r) =
      volume.withDensity fun Z => ENNReal.ofReal (frameRowDensity N r p Z) := by sorry

end PrivGaussMS
