-- Prove2me | Theorems.Thm_SelfSelReg_corollary_5_6
-- name    : SelfSelReg.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:16.766777+00:00
-- url     : https://prove2.me/theorems/d571a53a-56ee-4f61-8b14-68468a383f5e
-- title:
--   Corollary 5.6 — second conditional Hermite moment $\le e^{7s\log K+T^2/K^4}$
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$) under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, let $K\ge2$ and $T\ge1$ be reals and $s\ge1$ an integer. For every $i\in[k]$, every $1\le d\le 2s+1$, every $t\in[T,T+1]$ and every symmetric order-$d$ tensor $A$ with $\|A\|_F\le1$,
--   $$\Big(\mathbb E_{X,\xi_i}\big[\langle H_d(X),A\rangle^2\mid Y_i=t\big]\Big)^{1/2}\le e^{7s\log K+T^2/K^4}.$$
--
--   This is Proposition 5.5 specialized to $(G,Y)=(X,Y_i)$, in the form used in the proof of Theorem 5.1(i).
--
--   **Formalization Note** Here $K$, $T$ and $s$ are free parameters, as on the page (not the hyperparameters). The conditional expectation is the integral against the explicit conditional law `modelCondLaw` of Proposition 4.3. Natural logarithm.
--
--   Differences from the source:
--   - encoding: E[· | Y_i = t] and P(· | Y_i = t) for every t → integrals and measures under modelCondLaw w i t, the pushforward of the model law under (x, ξ) ↦ (x − c w_i, ξ − c e_i), c = (Y_i − t)/σ_i²; reason: this is the conditional Gaussian law of Proposition 4.3 for the jointly Gaussian vector (X, ξ, Y_i), defined for every t instead of almost everywhere
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Corollary 5.6, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_Tensor
import Definitions.Def_SelfSelReg_modelCondLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Corollary 5.6** (Second Conditional Hermite Moment).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Corollary 5.6, p.22 (PDF p.25): "Consider the Gaussian self-selection
model (Definition 1.1) under the boundedness and uncoveredness assumptions (Assumption 1.2). Let
K ≥ 2, T ≥ 1, and let s ≥ 1 be an integer. For every i ∈ [k], 1 ≤ d ≤ 2s + 1, t ∈ [T, T + 1], and
symmetric order-d tensor A with ‖A‖_F ≤ 1, (E_{X,ξ_i}[⟨H_d(X), A⟩² | Y_i = t])^{1/2} ≤ e^{7s log K + T²/K⁴}."

**Formalization Note.** `K` is a free real `K ≥ 2` here, not the hyperparameter, and `T`, `s` are free,
as on the page. `E[· | Y_i = t]` is the integral against the explicit conditional law
`modelCondLaw w i t` (Proposition 4.3). Natural logarithm. -/
theorem corollary_5_6 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hw : SatisfiesAssumption B Δ w) (K T : ℝ) (hK : 2 ≤ K) (hT : 1 ≤ T) (s : ℕ) (hs : 1 ≤ s)
    (i : Fin k) (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 2 * s + 1) (t : ℝ) (ht : T ≤ t) (ht' : t ≤ T + 1)
    (A : Tensor n d) (hA : IsSymmetricTensor A) (hAF : GaussPart.frobeniusNorm A ≤ 1) :
    Real.sqrt (∫ z, frobInner (GaussPart.hermiteTensor d z.1) A ^ 2 ∂(modelCondLaw w i t)) ≤
      Real.exp (7 * s * Real.log K + T ^ 2 / K ^ 4) := by sorry

end SelfSelReg
