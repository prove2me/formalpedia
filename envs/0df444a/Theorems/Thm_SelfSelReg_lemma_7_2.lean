-- Prove2me | Theorems.Thm_SelfSelReg_lemma_7_2
-- name    : SelfSelReg.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:51.258786+00:00
-- url     : https://prove2.me/theorems/1ca19f5c-c6b3-40e1-a6a1-62d1b7d81c8c
-- title:
--   Lemma 7.2 — moment bounds for restricted least squares
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$), suppose $\Delta\le\|w_i\|_2\le B$ for all $i$, with $B\ge1$, $\Delta\in(0,1]$, and let $K=16(1+B^2)^3/\Delta^4$. Let $\Gamma\ge1$, and let $\mathcal E_{\hat u}=\{\Gamma\le\langle\hat u,X\rangle\le\Gamma+1\}$ for a unit vector $\hat u$. Fix a unit vector $\hat u$ and $i\in[k]$ such that
--   $$\langle w_i-w_j,\hat u\rangle\ge\frac{\Delta^2}{2B}\qquad(j\ne i).$$
--   Then for every unit vector $v$ and every coordinate $j\in[n]$,
--   $$\mathbb E_X[\langle v,X\rangle^2\mid\mathcal E_{\hat u}]\le4\Gamma^2,\qquad\mathbb E_{X,\xi}[(Y_{\max}-Y_i)^2\mid\mathcal E_{\hat u}]\le6B^2k\,e^{-2\Gamma^2/K},\qquad\mathbb E_{X,\xi}[(X_jY_{\max}\mathbf 1_{\mathcal E_{\hat u}})^2]\le96B^2\log k .$$
--
--   On the large-projection event the maximum is nearly the response $Y_i$, and the coordinates of $XY_{\max}\mathbf 1_{\mathcal E_{\hat u}}$ have bounded second moments; this controls the bias and the sampling error of the restricted least squares estimate (Theorem 7.1).
--
--   **Formalization Note** $\mathbb E[\,\cdot\mid\mathcal E_{\hat u}]=\mathbb E[\,\cdot\,\mathbf 1_{\mathcal E_{\hat u}}]/\mathbb P(\mathcal E_{\hat u})$, a positive-probability event. Only boundedness is assumed, as on the page; $\Gamma$ is free. Natural logarithm.
--
--   Differences from the source:
--   - encoding: E[· | E_û] → E[· 1_{E_û}]/P(E_û); reason: E_û has positive probability; this is the elementary conditional expectation
--   - encoding: the coordinate index j ∈ [n] of the third bound → l : Fin n; reason: j is already used for regressor indices
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 7.2, p.50 (PDF p.53); E_û defined p.49 (PDF p.52)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_hypK

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Lemma 7.2** (Moment Bounds for Restricted Least Squares).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 7.2, p.50 (PDF p.53): "Consider the Gaussian self-selection model
(Definition 1.1) under the boundedness assumption (Assumption 1.2). Use K from Hyperparameters 4.1,
and let Γ ≥ 1. Fix a unit vector û and i ∈ [k] such that ⟨w_i − w_j, û⟩ ≥ ∆²/(2B) (j ≠ i). Then for
every unit vector v and every j ∈ [n], E_X[⟨v, X⟩² | E_û] ≤ 4Γ², E_{X,ξ}[(Y_max − Y_i)² | E_û] ≤
6B²k e^{−2Γ²/K}, E_{X,ξ}[(X_j Y_max 1_{E_û})²] ≤ 96B² log k."

**Formalization Note.**
* `E_û = {Γ ≤ ⟨û, X⟩ ≤ Γ + 1}` (p.49, PDF p.52), here with a free `Γ ≥ 1` as on the page (not the
  hyperparameter (12)). `E[· | E_û] = E[· 1_{E_û}]/P(E_û)`; `P(E_û) > 0` since `⟨û, X⟩ ∼ N(0, 1)`.
* "Boundedness" is the first half of Assumption 1.2 only, `∆ ≤ ‖w_i‖₂ ≤ B` for all `i`, with
  `B ≥ 1`, `∆ ∈ (0, 1]`; uncoveredness is not assumed, as on the page. `K = hypK B ∆`.
* The coordinate index `j ∈ [n]` of the third bound is named `l`, to keep `j` for regressor indices.
  Expectations are over `(X, ξ) ∼ jointLaw`; `Y_max = yMax w X ξ`. Natural logarithm. The integrands
  are polynomials in a Gaussian vector (times an indicator), hence integrable. -/
theorem lemma_7_2 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hbdd : ∀ i, Δ ≤ ‖w i‖ ∧ ‖w i‖ ≤ B) (Γ : ℝ) (hΓ : 1 ≤ Γ) (û : EuclideanSpace ℝ (Fin n))
    (hû : ‖û‖ = 1) (i : Fin k) (hgap : ∀ j, j ≠ i → Δ ^ 2 / (2 * B) ≤ inner ℝ (w i - w j) û)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) (l : Fin n) :
    (∫ z, inner ℝ v z.1 ^ 2 *
          Set.indicator {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) |
            Γ ≤ inner ℝ û z.1 ∧ inner ℝ û z.1 ≤ Γ + 1} 1 z ∂(jointLaw n k)) /
        (jointLaw n k).real {z | Γ ≤ inner ℝ û z.1 ∧ inner ℝ û z.1 ≤ Γ + 1} ≤ 4 * Γ ^ 2 ∧
      (∫ z, (yMax w z.1 z.2 - response w z.1 z.2 i) ^ 2 *
          Set.indicator {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) |
            Γ ≤ inner ℝ û z.1 ∧ inner ℝ û z.1 ≤ Γ + 1} 1 z ∂(jointLaw n k)) /
        (jointLaw n k).real {z | Γ ≤ inner ℝ û z.1 ∧ inner ℝ û z.1 ≤ Γ + 1} ≤
          6 * B ^ 2 * k * Real.exp (-2 * Γ ^ 2 / hypK B Δ) ∧
      ∫ z, (z.1 l * yMax w z.1 z.2 *
          Set.indicator {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) |
            Γ ≤ inner ℝ û z.1 ∧ inner ℝ û z.1 ≤ Γ + 1} 1 z) ^ 2 ∂(jointLaw n k) ≤
        96 * B ^ 2 * Real.log k := by sorry

end SelfSelReg
