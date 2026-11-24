-- Prove2me | Theorems.Thm_SongZhangKLS_cheeger_universal
-- name    : SongZhangKLS.cheeger_universal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T08:34:23.089019+00:00
-- url     : https://prove2.me/theorems/c94e37c1-0fbd-484b-9b06-4c1cf799b375
-- title:
--   Universal bound on the reciprocal Cheeger constant $\psi_\mu$ of isotropic log-concave measures
-- statement:
--   This is the isoperimetric half of Theorem 6.1 of Song–Zhang: the KLS constant $\psi_n$ is bounded by a universal constant.
--
--   There is a universal constant $C'>0$ such that for every $n\ge0$ and every isotropic log-concave probability measure $\mu$ on $\mathbb R^n$,
--
--   $$
--   \psi_\mu=\sup\Big\{\frac{\min\{\mu(A),1-\mu(A)\}}{\mu^+(A)}\;:\;A\ \text{Borel},\ 0<\mu(A)<1\Big\}\;\le\;C',
--   \qquad
--   \mu^+(A)=\liminf_{\varepsilon\to0^+}\frac{\mu(A+\varepsilon B_2^n)-\mu(A)}{\varepsilon}.
--   $$
--
--   Equivalently $\min\{\mu(A),1-\mu(A)\}\le C'\mu^+(A)$ for every Borel set $A$. Taking the supremum over $\mu$ gives $\psi_n\le C'$.
--
--   Mathematically this follows from the dimension-free Poincaré inequality for isotropic log-concave measures combined with the reverse Cheeger (Buser–Ledoux–E. Milman) inequality $\psi_\mu^2\lesssim C_P(\mu)$ for log-concave measures, the left half of eq. (2) of the paper up to the value of the absolute constant.
--
--   **Formalization Note** $\psi_\mu$ is `cheegerPsi` and $\mu^+$ is `outerBoundary` (values in $[0,\infty]$, one-sided limit inferior, Minkowski sum with the closed unit ball). Log-concavity and isotropy are the published `FunctionalInequalities.KLS.LogConcave` and `FunctionalInequalities.KLS.Isotropic`.
-- source:
--   Song, Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (October 2026), Theorem 6.1, p.63 (bound psi_n <= C'), via eq. (2), p.2; reverse Cheeger inequality: Ledoux, Spectral gap, logarithmic Sobolev constant, and geometric bounds (2004); E. Milman, Invent. Math. 177 (2009)

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_SongZhangKLS_cheegerPsi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SongZhangKLS
theorem cheeger_universal :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
      cheegerPsi (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal C' := by sorry
end SongZhangKLS
