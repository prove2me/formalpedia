-- Prove2me | Theorems.Thm_SongZhangKLS_eq_2
-- name    : SongZhangKLS.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:31.175195+00:00
-- url     : https://prove2.me/theorems/3b0d269b-a31f-4221-8f77-ca4cbaedf35a
-- title:
--   Eq. (2) — Cheeger and reverse Cheeger inequalities: $\psi_\mu^2/\pi\le C_P(\mu)\le4\psi_\mu^2$ for log-concave $\mu$
-- statement:
--   Let $\mu$ be a log-concave probability measure on $\mathbb R^n$ that is absolutely continuous with respect to Lebesgue measure. Then the reciprocal Cheeger constant and the Poincaré constant are comparable:
--   $$\frac{\psi_\mu^2}{\pi}\le C_P(\mu)\le4\cdot\psi_\mu^2. \tag{2}$$
--
--   The right inequality is Cheeger's inequality [Che70]; the left one is the reverse (Buser–Ledoux) inequality for log-concave measures [Bus82, Led04, Mil09, PM21]. The paper cites (2) without proof and uses it to pass from its Poincaré bound to the bound on $\psi_n$.
--
--   **Formalization Note** $C_P$ is eq. (1) with the $L^2$ requirement and $\psi_\mu$ uses the one-sided outer boundary measure; both lie in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: for log-concave measures → for log-concave probability measures $\mu$ with $\mu\ll$ Lebesgue measure; reason: $C_P$ is defined through $\nabla f$ for locally Lipschitz $f$ on $\mathbb R^n$, which exists only Lebesgue-almost everywhere; for a log-concave measure on a proper affine subspace of positive dimension the quantity in (1) is undefined, and for a point mass $\psi_\mu$ is a supremum over an empty family (no Borel $A$ with $0<\mu(A)<1$), so the condition only excludes undefined cases
--   - encoding: log-concave: $\mu(sA+(1-s)B)\ge\mu(A)^s\mu(B)^{1-s}$ for compact $A,B$ and $0\le s\le1$ → the published `FunctionalInequalities.KLS.LogConcave` (the same inequality for $0<s<1$); reason: the endpoints $s\in\{0,1\}$ are trivial for every measure under the paper's conventions, while the literal $s=0$, $A=\emptyset$ case with the convention $0^0=1$ would exclude every measure; same class
--   - encoding: $C_P(\mu)\in[0,+\infty]$, the least $C$ in (1) with the $L^2$ requirement, $+\infty$ if no finite $C$ works → `poincareConst`: an infimum in $[0,\infty]$ over finite $C\ge0$ (empty infimum $=\infty$), with $\nabla f$ the Mathlib `gradient` and the variance `evariance`; reason: Lean convention; the variance is nonnegative so only $C\ge0$ matter, and for measures absolutely continuous with respect to Lebesgue measure the gradient of a locally Lipschitz function exists almost everywhere (Rademacher); same values
--   - encoding: $\mu^+(A)=\liminf_{\varepsilon\to0}(\mu(A+\varepsilon B_2^n)-\mu(A))/\varepsilon$ and $\psi_\mu$, $\psi_n$ as real suprema → `outerBoundary` with $\varepsilon\to0^+$, and `cheegerPsi`, `psiN` as suprema in $[0,\infty]$; reason: the quotient divides by $\varepsilon$ and $A+\varepsilon B_2^n$ does not depend on the sign of $\varepsilon$, so only $\varepsilon>0$ is meaningful; an infinite ratio is $+\infty$ as in the source
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), §1, eq. (2), p.2

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_SongZhangKLS_poincareConst
import Definitions.Def_SongZhangKLS_cheegerPsi

open MeasureTheory
open scoped ENNReal

namespace SongZhangKLS

/-- **Eq. (2): Cheeger's inequality and its reverse for log-concave measures**, §1, p.2, of
Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

For log-concave measures, `ψ_µ²` and `C_P(µ)` are comparable up to absolute factors; using
Cheeger's inequality [Che70] and the reverse inequalities [Bus82, Led04, Mil09, PM21],
`ψ_µ²/π ≤ C_P(µ) ≤ 4 · ψ_µ²`.

**Formalization Note.** `µ` is a log-concave probability measure on `ℝⁿ` (the published
`FunctionalInequalities.KLS.LogConcave`) that is absolutely continuous with respect to Lebesgue
measure: `C_P` uses `∇f`, which is only meaningful `µ`-almost everywhere when `µ ≪` Lebesgue.
`ψ_µ = cheegerPsi` and `C_P = poincareConst` are in `ℝ≥0∞`. -/
theorem eq_2 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hlc : FunctionalInequalities.KLS.LogConcave μ)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume) :
    cheegerPsi (μ : Measure (EuclideanSpace ℝ (Fin n))) ^ 2 / ENNReal.ofReal Real.pi ≤
        poincareConst (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      poincareConst (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
        4 * cheegerPsi (μ : Measure (EuclideanSpace ℝ (Fin n))) ^ 2 := by sorry

end SongZhangKLS
