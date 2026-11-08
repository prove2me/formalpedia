-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_49
-- name    : SpencerEight.lemma_8_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:38.497129+00:00
-- url     : https://prove2.me/theorems/063975e8-5513-40b5-90a1-6dd26130de4b
-- title:
--   Lemma 8.49 — shifted cubic constraints for the initial envelope
-- statement:
--   For $a>0$, $t\ge0$ and a standard Gaussian $\xi$, define $G_3(a,t):=\mathbb E[(\sqrt a|\xi|-t)_+^3]$. Let $N_1,\dots,N_m\in\mathbb R^{n\times n}$ be symmetric, put $Z:=\sum_{i=1}^m\xi_iN_i$, and suppose $\sum_iN_i^2\preceq aI$. Then
--   $$\mathbb E\bigl[\operatorname{tr}[(|Z|-tI)_+^3]\bigr]\le nG_3(a,t).$$
--   If $b:=t/\sqrt a$, $\varphi(b):=(2\pi)^{-1/2}e^{-b^2/2}$ and $\Phi(b):=\Pr[\xi\ge b]$, then
--   $$G_3(a,t)=2\bigl((t^2+2a)\sqrt a\,\varphi(b)-(t^3+3at)\Phi(b)\bigr).\tag{126}$$
--
--   The comparison reduces a spectral hinge moment to a scalar Gaussian integral with a closed form.
--
--   Differences from the source:
--   - encoding: expectations → Integrable together with a Bochner integral bound, for both the matrix statistic and G₃; reason: the statistics have polynomial growth, and the integrability is stated so that the integrals are not junk values
--   - encoding: (|Z| − tI)³₊ → the functional calculus of x ↦ (|x| − t)³₊ at Z; reason: Section 4.1 defines f(X) by the eigenvalue formula
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.49, p.109 (PDF p.109)

import Mathlib
import Definitions.Def_SpencerEight_G3
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_signedSum
open MeasureTheory ProbabilityTheory

namespace SpencerEight

/-- Lemma 8.49 (Shifted cubic constraints for the initial envelope), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.109 (PDF p.109). The comparison `E[tr[(|Z| − tI)³₊]] ≤ n G₃(a, t)` and the identity (126).

**Formalization Note** `(|Z| − tI)³₊` is the functional calculus of `x ↦ (|x| − t)³₊`. `Φ(b) = Pr[ξ ≥ b]` is the upper tail. `Integrable` is part of the conclusion. -/
theorem lemma_8_49 {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (∀ (m n : ℕ) (N : Fin m → Matrix (Fin n) (Fin n) ℝ), (∀ i, (N i).IsSymm) →
      (a • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ i, N i ^ 2).PosSemidef →
      Integrable (fun ξ : Fin m → ℝ =>
        (cfc (fun x : ℝ => (max (|x| - t) 0) ^ 3) (signedSum N ξ)).trace) (gammaM (Fin m)) ∧
      ∫ ξ, (cfc (fun x : ℝ => (max (|x| - t) 0) ^ 3) (signedSum N ξ)).trace ∂(gammaM (Fin m)) ≤
        n * G3 a t) ∧
    Integrable (fun x : ℝ => (max (Real.sqrt a * |x| - t) 0) ^ 3) (gaussianReal 0 1) ∧
    G3 a t = 2 * ((t ^ 2 + 2 * a) * Real.sqrt a *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t / Real.sqrt a) ^ 2 / 2)) -
      (t ^ 3 + 3 * a * t) * (gaussianReal 0 1 (Set.Ici (t / Real.sqrt a))).toReal) := by sorry

end SpencerEight
