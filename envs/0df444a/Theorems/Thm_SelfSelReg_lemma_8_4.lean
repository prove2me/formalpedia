-- Prove2me | Theorems.Thm_SelfSelReg_lemma_8_4
-- name    : SelfSelReg.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:02.836074+00:00
-- url     : https://prove2.me/theorems/477010b1-6daa-4ecf-9484-4c538a771ea9
-- title:
--   Lemma 8.4 — peeling bias identity (114) and bound
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$), fix $R\subsetneq[k]$ and put $Q=[k]\setminus R$; let $X'$ be a random element independent of the covariate and noises.
--
--   1. **(i)** For every integrable scalar- or matrix-valued function $\psi(X,X')$,
--   $$\mathbb E\big[\psi(X,X')\,\omega_R(X,Y_{\max})\big]-\mathbb E\big[\psi(X,X')\,\mathbf 1\{T\le Y_{\max,Q}\le T+1\}\big]=-\mathbb E\big[\psi(X,X')\,\mathbf 1\{T\le\min\{Y_{\max,R},Y_{\max,Q}\}\le T+1\}\big].$$
--   2. **(ii)** Suppose Assumption 1.2 holds with constants $B\ge1$, $\Delta\in(0,1]$, let $K=16(1+B^2)^3/\Delta^4$, let $s\ge1$ be an integer and $T>0$ with $T^2\ge Ks$. If $X'\sim N(0,I_n)$ and $\psi(X,X')$ is a real polynomial of degree at most $2s+1$, then for every $1\le r\le s$,
--   $$\Big|\mathbb E\big[\psi(X,X')\,\mathbf 1\{T\le\min\{Y_{\max,R},Y_{\max,Q}\}\le T+1\}\big]\Big|\le k\,e^{4s\log K-T^2/(2K)}\,\|\psi\|_{L^2(X,X')}\,\mathrm{tr}(A^{(r)}_Q).$$
--
--   Here $\omega_R$ is the ideal signed peeling weight and $A^{(r)}_Q=\sum_{i\in Q}\lambda_i^{(2r)}u_i^{\otimes r}(u_i^{\otimes r})^\top$. Using $\omega_R$ in place of the slice indicator of the unrecovered maximum thus costs a bias that is exponentially small relative to the total weight of the remaining components.
--
--   **Formalization Note** In (i), $X'$ takes values in an arbitrary measurable space with a probability law, independent of $(X,\xi)$ (product measure), and $\psi$ takes values in any real Banach space. In (ii), $\psi$ is a multivariate polynomial in the $2n$ coordinates of $(X,X')$ of total degree at most $2s+1$. For $R=\emptyset$ the min-slice event is empty.
--
--   Differences from the source:
--   - generalization: ψ scalar- or matrix-valued → ψ with values in any real Banach space V; reason: scalars and matrices (with any norm) are such spaces, and the identity is linear in ψ
--   - generalization: in (i), T is the hyperparameter of Hyperparameters 4.1 → every real T in (i); reason: the identity holds for every threshold and specializes to the hyperparameter
--   - encoding: X′ a random element independent of the covariate and noises → X′ with law μ′ on a measurable space Ω′ (in Type), independence as the product measure; reason: the expectations depend only on the joint law
--   - encoding: a real polynomial ψ(X, X′) of degree at most 2s + 1 → ψ : MvPolynomial (Fin n ⊕ Fin n) ℝ with totalDegree ≤ 2s + 1; reason: same polynomials
--   - encoding: 1{T ≤ min{Y_max,R, Y_max,Q} ≤ T + 1} → inMinSlice: T ≤ Y_max,R, T ≤ Y_max,Q, and (Y_max,R ≤ T + 1 or Y_max,Q ≤ T + 1); reason: the same event, with Y_max,∅ = −∞
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 8.4, (114), p.59 (PDF p.62); proof §8.4, p.62 (PDF p.65)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment
import Definitions.Def_SelfSelReg_peelWeight

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Lemma 8.4** (Peeling Bias Bound), parts (i) and (ii).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 8.4, p.59 (PDF p.62): "Consider the Gaussian self-selection model
(Definition 1.1). Fix R ⊊ [k], put Q = [k] \ R, and let X′ be a random element independent of the
covariate and noises. (i) For every integrable scalar- or matrix-valued function ψ(X, X′),
E_{X,ξ,X′}[ψ(X, X′) ω_R(X, Y_max)] − E_{X,ξ,X′}[ψ(X, X′) 1{T ≤ Y_max,Q ≤ T + 1}]
= −E_{X,ξ,X′}[ψ(X, X′) 1{T ≤ min{Y_max,R, Y_max,Q} ≤ T + 1}]. (114) (ii) Suppose the boundedness and
uncoveredness assumptions (Assumption 1.2) hold, and use the choice of K from Hyperparameters 4.1.
Let s ≥ 1 be an integer and suppose T > 0 and T² ≥ Ks. If X′ ∼ N(0, I_n) and ψ(X, X′) is a real
polynomial of degree at most 2s + 1, then for every 1 ≤ r ≤ s,
|E_{X,ξ,X′}[ψ(X, X′) 1{T ≤ min{Y_max,R, Y_max,Q} ≤ T + 1}]| ≤ k e^{4s log K − T²/(2K)} ‖ψ‖_{L²(X,X′)} tr(A^{(r)}_Q)."

**Formalization Note.**
* (i): `X′` takes values in an arbitrary measurable space `Ω′` with a probability law `μ′`,
  independent of `(X, ξ)` (product measure); `ψ` takes values in any real Banach space `V`, which
  covers scalar and matrix values (a generalization), and is integrable for the law of `(X, X′)`.
  `T` is any real (the paper's `T` is the hyperparameter; a generalization: the identity holds for
  every threshold).
* (ii): `K = hypK B ∆`; `s`, `T` free, as on the page. `ψ` is a real polynomial in the `2n` coordinates
  of `(X, X′)` of total degree at most `2s + 1`; `‖ψ‖_{L²(X,X′)} = (E ψ²)^{1/2}`;
  `A^{(r)}_Q = evenTarget w T Q r` (38).
* `ω_R = peelWeight T w R` (104); `T ≤ min{Y_max,R, Y_max,Q} ≤ T + 1` is `inMinSlice`, empty for
  `R = ∅` (`Y_max,∅ = −∞`). -/
theorem lemma_8_4 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ) (R : Finset (Fin k)) (hR : R ≠ Finset.univ) :
    -- (i)
    (∀ (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
      (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (ψ : EuclideanSpace ℝ (Fin n) × Ω' → V),
      Integrable ψ ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod μ') →
      (∫ p, peelWeight T w R p.1.1 (yMax w p.1.1 p.1.2) • ψ (p.1.1, p.2)
            ∂((jointLaw n k).prod μ')) -
          ∫ p, Set.indicator {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) × Ω' |
              inSlice T w (Finset.univ \ R) p.1.1 p.1.2} (fun p => ψ (p.1.1, p.2)) p
            ∂((jointLaw n k).prod μ') =
        -∫ p, Set.indicator {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) × Ω' |
              inMinSlice T w R (Finset.univ \ R) p.1.1 p.1.2} (fun p => ψ (p.1.1, p.2)) p
            ∂((jointLaw n k).prod μ')) ∧
    -- (ii)
    (∀ (B Δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 → SatisfiesAssumption B Δ w →
      ∀ s : ℕ, 1 ≤ s → 0 < T → hypK B Δ * s ≤ T ^ 2 →
      ∀ ψ : MvPolynomial (Fin n ⊕ Fin n) ℝ, ψ.totalDegree ≤ 2 * s + 1 →
      ∀ r : ℕ, 1 ≤ r → r ≤ s →
        |∫ p, MvPolynomial.eval (Sum.elim (fun a => p.1.1 a) (fun a => p.2 a)) ψ *
            Set.indicator {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) ×
                EuclideanSpace ℝ (Fin n) |
              inMinSlice T w R (Finset.univ \ R) p.1.1 p.1.2} 1 p
            ∂((jointLaw n k).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))| ≤
          (k : ℝ) * Real.exp (4 * s * Real.log (hypK B Δ) - T ^ 2 / (2 * hypK B Δ)) *
            Real.sqrt (∫ q, MvPolynomial.eval (Sum.elim (fun a => q.1 a) (fun a => q.2 a)) ψ ^ 2
              ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
                (stdGaussian (EuclideanSpace ℝ (Fin n))))) *
            Matrix.trace (evenTarget w T (Finset.univ \ R) r)) := by sorry

end SelfSelReg
