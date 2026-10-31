-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P51_gaussian_infiniteBandwidth
-- name    : QAlgorithms.Papers.Independent.Intake100.P51.gaussian_infiniteBandwidth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:42:05.372394+00:00
-- url     : https://prove2.me/theorems/53ddcbb6-ff48-4a52-b60f-a063ec6c347a
-- title:
--   Infinite-bandwidth Gaussian variational secrecy capacity
-- statement:
--   Let $P\ge0$ and $N_1,N_2>0$. For each bandwidth $B>0$, let $X$ have any probability law on $\mathbb R$ with finite second moment satisfying $\mathbb E[X^2]\le P$. Independently of $X$, let $W_1$ and $W_2$ be independent centered Gaussians of variances $N_1B$ and $N_2B$. Define $Y=X+W_1$ and $Z=X+W_1+W_2$, and define the finite-bandwidth variational value in nats per second by
--
--   $$
--   C_s(B)=2B\sup_{\operatorname{law}(X):\,\mathbb E[X^2]\le P}\bigl(I(X;Y)-I(X;Z)\bigr).
--   $$
--
--   The limit exists and satisfies
--
--   $$
--   \lim_{B\to\infty} C_s(B)=\frac{P}{N_1}-\frac{P}{N_1+N_2}.
--   $$
--
--   This is the introduction's Gaussian illustration of an infinite-bandwidth converse. The factor $2B$ converts scalar uses to uses per second.
--
--   **Formalization Note** The input and noises are constructed on their product probability space. The real information difference is well-defined because finite input power and positive noise variances imply finite mutual information. The supremum set is nonempty and bounded for the stated positive parameters; the limit filter uses eventually positive bandwidths.
-- source:
--   The Degraded Poisson Wiretap Channel, arXiv:1004.0269v1, PDF p. 6, Unnumbered introduction result: infinite-bandwidth Gaussian illustration

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P51

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P51

open MeasureTheory Filter

open InformationTheory (klDiv)

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Unnumbered Gaussian illustration, PDF pp.4–6, Eqs.(2)–(4): existence
and value of the infinite-bandwidth limit of the specified variational
capacity. Bandwidth tends to positive infinity, so is eventually positive;
zero power is permitted, while both noise spectral densities are positive. -/
theorem gaussian_infiniteBandwidth (P N1 N2 : ℝ)
    (hP : 0 ≤ P) (hN1 : 0 < N1) (hN2 : 0 < N2) :
    Tendsto (fun B : ℝ => gaussianSecrecyValue B P N1 N2) atTop
      (nhds (P / N1 - P / (N1 + N2))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P51

end
