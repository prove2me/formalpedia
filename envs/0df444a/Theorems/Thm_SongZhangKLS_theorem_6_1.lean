-- Prove2me | Theorems.Thm_SongZhangKLS_theorem_6_1
-- name    : SongZhangKLS.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:41.089525+00:00
-- url     : https://prove2.me/theorems/e102c8bd-fa70-4077-92b0-e6f84e164dae
-- title:
--   Theorem 6.1 — universal Poincaré and KLS bounds: $C_P(\mu)\le C$, $\psi_n\le C'$, and finite Dirichlet energy implies $L^2$
-- statement:
--   There are universal constants $C,C'>0$ such that, for every $n\ge1$ and every isotropic log-concave probability measure $\mu$ on $\mathbb R^n$,
--   $$C_P(\mu)\le C,\qquad\psi_n\le C'.$$
--   In particular, every locally Lipschitz $f:\mathbb R^n\to\mathbb R$ with $\int\|\nabla f\|^2\,d\mu<\infty$ belongs to $L^2(\mu)$ and satisfies
--   $$\mathrm{Var}_\mu[f]\le C\int\|\nabla f\|^2\,d\mu.$$
--
--   This is the formal version of the paper's Theorem 1.1, the Kannan–Lovász–Simonovits conjecture: the isoperimetric constant of an isotropic log-concave measure is bounded independently of the dimension.
--
--   **Formalization Note** $C$ and $C'$ are chosen before $n$, $\mu$ and $f$. $C_P$ is eq. (1) with the $L^2$ requirement, $\psi_n$ the supremum of $\psi_\mu$ over isotropic log-concave probability measures on $\mathbb R^n$; both lie in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: log-concave: $\mu(sA+(1-s)B)\ge\mu(A)^s\mu(B)^{1-s}$ for compact $A,B$ and $0\le s\le1$ → the published `FunctionalInequalities.KLS.LogConcave` (the same inequality for $0<s<1$); reason: the endpoints $s\in\{0,1\}$ are trivial for every measure under the paper's conventions, while the literal $s=0$, $A=\emptyset$ case with the convention $0^0=1$ would exclude every measure; same class
--   - encoding: isotropic: $\int x\,d\mu=0$ and $\int x\otimes x\,d\mu=I_n$ → the published `FunctionalInequalities.KLS.Isotropic` (finite second moment, mean $0$, centered covariance operator the identity); reason: finite second moments are implicit in the source's definition; same measures
--   - encoding: $C_P(\mu)\in[0,+\infty]$, the least $C$ in (1) with the $L^2$ requirement, $+\infty$ if no finite $C$ works → `poincareConst`: an infimum in $[0,\infty]$ over finite $C\ge0$ (empty infimum $=\infty$), with $\nabla f$ the Mathlib `gradient` and the variance `evariance`; reason: Lean convention; the variance is nonnegative so only $C\ge0$ matter, and for measures absolutely continuous with respect to Lebesgue measure the gradient of a locally Lipschitz function exists almost everywhere (Rademacher); same values
--   - encoding: $\mu^+(A)=\liminf_{\varepsilon\to0}(\mu(A+\varepsilon B_2^n)-\mu(A))/\varepsilon$ and $\psi_\mu$, $\psi_n$ as real suprema → `outerBoundary` with $\varepsilon\to0^+$, and `cheegerPsi`, `psiN` as suprema in $[0,\infty]$; reason: the quotient divides by $\varepsilon$ and $A+\varepsilon B_2^n$ does not depend on the sign of $\varepsilon$, so only $\varepsilon>0$ is meaningful; an infinite ratio is $+\infty$ as in the source
--   - encoding: $\mathrm{Var}_\mu[\cdot]$ → `evariance` (variance in $[0,\infty]$); reason: Lean convention; a finite bound on `evariance` is the source's variance bound, without the junk value $0$ of the real variance outside $L^2$
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Theorem 6.1, p.63

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_SongZhangKLS_poincareConst
import Definitions.Def_SongZhangKLS_cheegerPsi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SongZhangKLS

/-- **Theorem 6.1 (Main result, formal version of Theorem 1.1)**, p.63, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

For every `n ≥ 1` and every isotropic log-concave probability measure `µ` on `ℝⁿ`,
`C_P(µ) ≤ C` and `ψ_n ≤ C′`, where `C, C′ > 0` are two universal constants. In particular, every
locally Lipschitz `f` with `∫ ‖∇f‖² dµ < ∞` belongs to `L²(µ)` and satisfies
`Var_µ[f] ≤ C ∫ ‖∇f‖² dµ`.

**Formalization Note.** The constants `C, C′` are chosen before `n`, `µ` and `f`. `C_P` is
`poincareConst` (eq. (1), in `ℝ≥0∞`, `+∞` when no finite constant works or a finite-energy
function is not in `L²`), `ψ_n` is `psiN` (in `ℝ≥0∞`), the Dirichlet energy is
`dirichletEnergy` (`∫⁻ ‖∇f‖²`, with Mathlib's `gradient`), and the variance is `evariance`.
Log-concave and isotropic are the published `FunctionalInequalities.KLS.LogConcave` and
`FunctionalInequalities.KLS.Isotropic`. -/
theorem theorem_6_1 :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ n : ℕ, 1 ≤ n →
      (∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
          poincareConst (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal C ∧
          ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
            dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f < ⊤ →
              MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
              evariance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                ENNReal.ofReal C * dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f) ∧
      psiN n ≤ ENNReal.ofReal C' := by sorry

end SongZhangKLS
