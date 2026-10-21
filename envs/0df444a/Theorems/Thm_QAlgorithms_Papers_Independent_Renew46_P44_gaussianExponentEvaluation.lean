-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_gaussianExponentEvaluation
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.gaussianExponentEvaluation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:40:48.268638+00:00
-- url     : https://prove2.me/theorems/0c33828c-8690-42dd-abcc-d9a46a13ef68
-- title:
--   §V.2, (96)–(99): Gaussian-prior exponent calculations
-- statement:
--   Fix $E>0$ and the circular Gaussian prior of mean energy $E$ for coherent-state signals. Let $\mu(E,s,p)$ and $\widetilde\mu(E,s,p)$ denote the tilted operator-power and overlap integrals from (78)-(79), with cost $|z|^2$. For $0\le p<E^{-1}$,
--
--   $$\mu(E,s,p)=(1+s)pE+\log[(1+E-pE)^{1+s}-E^{1+s}],\quad s\ge0,$$
--
--   $$\widetilde\mu(E,s,p)=s\{2pE+\log[1+p^2E^2-2pE+2E(1-pE)/s]\},\quad s>0.$$
--
--   For $s>0$, stationarity of the first function in $p$ is equivalent to $(1+E-pE)^s(1-p)=E^s$. Put
--
--   $$q(E)=\frac{1+\sqrt{4E^2+1}}2,\qquad p_1(E)=1+E^{-1}-q(E)/E.$$
--
--   Then $0\le p_1<E^{-1}$ is the unique admissible root at $s=1$, and
--
--   $$\partial_s\mu(E,0,0)=g(E),\quad
--   \mu(E,1,p_1)=2(E+1-q)+\log q,$$
--
--   $$\partial_s\mu(E,1,p_1)=E+1-q+\frac{q^2\log q-E^2\log E}{q^2-E^2}.$$
--
--   For $s\ge1$, the expurgated stationarity equation is $p^2-2p(1/s+1/(2E))+1/(sE)=0$. Its unique admissible root is $p_s=1/s+1/E-q(E/s)/E$, and
--
--   $$\widetilde\mu(E,s,p_s)=2(E+s-sq(E/s))+s\log q(E/s).$$
--
--   These are exact fixed-prior evaluations; they assert no optimization over all input laws.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 26, §V.2, (96)–(99): Gaussian-prior exponent calculations

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Exact fixed-Gaussian-prior calculations, PDF pp.26-27, (96)-(99).
E>0 excludes singular density formulas. No optimization over all priors is
asserted, and these identities are not definitions of operational capacity. -/
theorem gaussianExponentEvaluation (E : ℝ) (hE : 0 < E) :
    (∀ s p : ℝ, 0 ≤ s → 0 ≤ p → p < 1 / E →
      gaussianMu E s p = (1 + s) * p * E +
        Real.log ((1 + E - p * E) ^ (1 + s) - E ^ (1 + s))) ∧
    (∀ s p : ℝ, 0 < s → 0 ≤ p → p < 1 / E →
      gaussianExpurgatedMu E s p =
        s * (2 * p * E + Real.log (1 + p ^ 2 * E ^ 2 - 2 * p * E +
          2 * E * (1 - p * E) / s))) ∧
    (∀ s p : ℝ, 0 < s → 0 ≤ p → p < 1 / E →
      (deriv (fun r => gaussianMu E s r) p = 0 ↔
        (1 + E - p * E) ^ s * (1 - p) = E ^ s)) ∧
    deriv (fun s => gaussianMu E s 0) 0 = g E ∧
    0 ≤ gaussianP E ∧ gaussianP E < 1 / E ∧
    (∀ p : ℝ, 0 ≤ p → p < 1 / E →
      ((1 + E - p * E) * (1 - p) = E ↔ p = gaussianP E)) ∧
    gaussianMu E 1 (gaussianP E) =
      2 * (E + 1 - gaussianQ E) + Real.log (gaussianQ E) ∧
    deriv (fun s => gaussianMu E s (gaussianP E)) 1 =
      E + 1 - gaussianQ E +
        ((gaussianQ E) ^ 2 * Real.log (gaussianQ E) - E ^ 2 * Real.log E) /
          ((gaussianQ E) ^ 2 - E ^ 2) ∧
    (∀ s : ℝ, 1 ≤ s →
      0 ≤ gaussianExpurgatedP E s ∧ gaussianExpurgatedP E s < 1 / E ∧
      (∀ p : ℝ, 0 ≤ p → p < 1 / E →
        (deriv (fun r => gaussianExpurgatedMu E s r) p = 0 ↔
          p ^ 2 - 2 * p * (1 / s + 1 / (2 * E)) + 1 / (s * E) = 0) ∧
        (p ^ 2 - 2 * p * (1 / s + 1 / (2 * E)) + 1 / (s * E) = 0 ↔
          p = gaussianExpurgatedP E s)) ∧
      gaussianExpurgatedMu E s (gaussianExpurgatedP E s) =
        2 * (E + s - s * gaussianQ (E / s)) + s * Real.log (gaussianQ (E / s))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
