-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_Supplement_theorem_3_3
-- name    : RandomDimReduction.Channel.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:44:01.957211+00:00
-- url     : https://prove2.me/theorems/6d53b8e1-5a78-4988-8c1c-2e312272c69c
-- title:
--   Theorem 3.3 — sample-optimal pure-state tomography
-- statement:
--   Let $d\ge1$, let $\psi\in\mathbb C^d$ be any unit vector, and let $n\ge1$. The effects $E_n(u)=d[n](|u\rangle\langle u|)^{\otimes n}$ are positive and integrate against sphere Haar $du$ to the orthogonal symmetric projector $\Pi_{sym}^n$. The complementary effect $I-\Pi_{sym}^n$ is positive and has zero probability on $\psi^{\otimes n}$. The actual outcome law is the probability measure $d\mu_{\psi,n}(u)=d[n]|\langle u,\psi\rangle|^{2n}du$, supported on unit vectors; its density agrees with the trace of $E_n(u)$ against the input state. Writing $F(u,\psi)=|\langle u,\psi\rangle|^2$,
--   $$\mathbb E_{\mu_{\psi,n}}F=\frac{n+1}{n+d},\qquad \Pr_{\mu_{\psi,n}}[F<1-\delta]\le\frac{d-1}{(n+d)\delta}\quad(\delta>0).$$
--   Consequently, for every $\delta>0$ and $n\ge\lceil10d/\delta\rceil$, the specified measurement returns fidelity at least $1-\delta$ with probability at least $9/10$. For $0<\delta\le1$, the positive choice $n=\lceil10d/\delta\rceil\le11d/\delta$ realizes the sample bound with global constants 11 and 1. Effect and fidelity integrability are conclusions as well.
--
--   This is the paper's sample-optimal continuous-POVM pure-state tomography guarantee, with the constants extracted from Eq. (8).
--
--   Differences from the source:
--   - encoding: Haar probability on the unit sphere and fidelity of pure states → the first-column Haar pushforward on Euclidean space, with probability-one unit support, and squared inner-product norm; reason: the ambient measure realizes the same sphere outcomes without postselection
--   - generalization: O(d/δ) copies give fidelity 1-O(δ) with success at least 9/10 → the explicit Eq. (8) mean, Markov tail for every δ>0, and the success guarantee for every n≥ceil(10d/δ), including a ceiling choice at most 11d/δ for 0<δ≤1; reason: Eq. (8) gives mean infidelity (d−1)/(n+d); Markov yields the displayed tail, hence these global constants and the full printed asymptotic claim
--   - encoding: the covariant POVM on the symmetric input subspace → positive effect density integrates to the orthogonal symmetric projector, with complementary effect I−Π having zero input probability and a normalized Born law; reason: this makes the measurement on the full input space explicit without any conditional outcome law
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, Theorem 3.3, p. 10

import Definitions.Def_RandomDimReduction_Channel_Supplement_Tomography

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Kronecker Matrix ComplexOrder ComplexConjugate Matrix.Norms.Elementwise InnerProductSpace

namespace RandomDimReduction.Channel.Supplement

/-- Theorem 3.3, pp.10–11: the specified continuous POVM, its actual Born law,
Eq.(8), the Markov tail, and global constants 11 copies and 1 infidelity.
The effect integral is the identity on the symmetric subspace; the complement is a
zero-probability outcome on the input. No normalization or integrability is assumed. -/
theorem theorem_3_3 (d : ℕ) (hd : 0 < d) (psi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) :
    IsProbabilityMeasure (sphereHaar d) ∧
    sphereHaar d {u | ‖u‖ = 1} = 1 ∧
    ∀ n : ℕ, 0 < n →
      MixedCloning.Optimal.symProjector (Fin d) n = subspaceProjector (symmetricSpace n d) ∧
      (∀ u : EuclideanSpace ℂ (Fin d), (covariantEffect n u).PosSemidef) ∧
      ((∀ i j : Word n d, Integrable (fun u => covariantEffect n u i j) (sphereHaar d))) ∧
      (fun i j => ∫ u, covariantEffect n u i j ∂sphereHaar d) = MixedCloning.Optimal.symProjector (Fin d) n ∧
      (1 - MixedCloning.Optimal.symProjector (Fin d) n).PosSemidef ∧
      ((1 - MixedCloning.Optimal.symProjector (Fin d) n) *
        tensor n (MixedCloning.Optimal.pure psi)).trace = 0 ∧
      (∀ u : EuclideanSpace ℂ (Fin d),
        (covariantEffect n u * tensor n (MixedCloning.Optimal.pure psi)).trace =
          ((MixedCloning.Optimal.symDimension d n : ℝ) * pureFidelity u psi ^ n : ℂ)) ∧
      IsProbabilityMeasure (bornLaw n psi) ∧
      bornLaw n psi {u | ‖u‖ = 1} = 1 ∧
      Integrable (fun u => pureFidelity u psi) (bornLaw n psi) ∧
      (∫ u, pureFidelity u psi ∂bornLaw n psi) = ((n : ℝ) + 1) / ((n : ℝ) + d) ∧
      (∀ delta : ℝ, 0 < delta →
        (bornLaw n psi {u | pureFidelity u psi < 1 - delta}).toReal ≤
          ((d : ℝ) - 1) / (((n : ℝ) + d) * delta)) ∧
      (∀ delta : ℝ, 0 < delta → ⌈10 * (d : ℝ) / delta⌉₊ ≤ n →
        ENNReal.ofReal (9 / 10 : ℝ) ≤ bornLaw n psi {u | 1 - delta ≤ pureFidelity u psi}) ∧
      (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        0 < ⌈10 * (d : ℝ) / delta⌉₊ ∧
        (⌈10 * (d : ℝ) / delta⌉₊ : ℝ) ≤ 11 * (d : ℝ) / delta ∧
        ENNReal.ofReal (9 / 10 : ℝ) ≤
          bornLaw ⌈10 * (d : ℝ) / delta⌉₊ psi {u | 1 - delta ≤ pureFidelity u psi}) := by sorry

end RandomDimReduction.Channel.Supplement
