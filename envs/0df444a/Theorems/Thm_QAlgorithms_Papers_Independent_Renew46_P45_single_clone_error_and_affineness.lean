-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_single_clone_error_and_affineness
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.single_clone_error_and_affineness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:43:40.728275+00:00
-- url     : https://prove2.me/theorems/2b3e06b2-a10a-406d-8744-75e8450e1d79
-- title:
--   Marginal operator identity, absolute error, and affine coefficient
-- statement:
--   Let $d\ge2$, $N\ge1$ and $M>N$. Let $T:B((\mathbb C^d)^{\otimes M})\to B(K)$ be a complex-linear CP unital cloning map, covariant under the actual tensor action and invariant under every output permutation, where $K=\operatorname{Sym}^N\mathbb C^d$. Let $\omega(T)\in\mathbb R$ be its generator coefficient, normalized by $T(\sum_{k=1}^M a_{(k)})=\omega(T)\left.\sum_{l=1}^N a_{(l)}\right|_K$ for traceless $a$. For every effect $0\le a\le I$ and every output site $k$,
--   $$
--   T(a_{(k)})=\frac{\operatorname{tr}a}{d}\left(1-\frac{N\omega(T)}M\right)I_K+\frac{\omega(T)}M\left.\sum_{l=1}^N a_{(l)}\right|_K.
--   $$
--   Writing $\gamma(T)=N\omega(T)/M$, its worst-case pure-state single-clone error is
--   $$
--   \Delta_{\mathrm{one}}(T)=\frac{d-1}{d}\left|1-\frac NM\omega(T)\right|=\frac{d-1}{d}|1-\gamma(T)|.
--   $$
--   For any other such map $S$ and $0\le t\le1$,
--   $$
--   \omega(tT+(1-t)S)=t\omega(T)+(1-t)\omega(S).
--   $$
--   Thus the coefficient is affine, with its normalization fixed by the marginal identity. No bound $\omega\le M/N$ is assumed.
--
--   **Formalization Note** The coefficient is computed from the summed output observable $\operatorname{diag}(1,-1,0,\ldots)$ on the input $|0\rangle^{\otimes N}$ and divided by $N$; it is not an arbitrary witness.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 5, §III B, Eq.(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.5 Eq.(11): operator marginal, absolute error and affineness.
No pre-optimization restriction omega≤M/N is assumed. -/
theorem single_clone_error_and_affineness (d N M : ℕ) (hd : 2 ≤ d)
    (hN : 1 ≤ N) (hNM : N < M) (T : CloneFunction d N M)
    (hT : IsCloning T) (hcov : IsCloningCovariant T) (hperm : IsPermutationInvariant T) :
    (∀ a : Mat d, IsEffect a → ∀ k : Fin M,
      T (siteObservable a k) =
        (Matrix.trace a / (d : ℂ) *
          (1 - (N : ℂ) * (cloneCoefficient (d := d) (by omega) T : ℂ) / M)) • boseProjector d N +
        ((cloneCoefficient (d := d) (by omega) T : ℂ) / M) • boseGenerator d N a) ∧
    cloningError T = ((d : ℝ) - 1) / d *
      |1 - (N : ℝ) / M * cloneCoefficient (d := d) (by omega) T| ∧
    (∀ S : CloneFunction d N M, IsCloning S → IsCloningCovariant S → IsPermutationInvariant S →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      cloneCoefficient (d := d) (by omega) (mixCloners t T S) =
        t * cloneCoefficient (d := d) (by omega) T +
          (1 - t) * cloneCoefficient (d := d) (by omega) S) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
