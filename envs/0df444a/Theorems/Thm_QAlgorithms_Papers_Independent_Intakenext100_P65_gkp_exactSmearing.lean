-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_gkp_exactSmearing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.gkp_exactSmearing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:40:31.908409+00:00
-- url     : https://prove2.me/theorems/f46b2f3c-274e-468d-8eaf-02df658b9716
-- title:
--   Exact weak displacement kernel and Gaussian smearing
-- statement:
--   Let $\mu,
--   u\in\{0,1\}$, $0<\Delta\le1$, and $z\in\mathbb C$. For $n=(n_1,n_2)\in\mathbb Z^2$, put $\Lambda_n=\sqrt{\pi/2}(2n_1+\mu-
--   u+in_2)$ and $s_n=e^{i\pi(n_1+(\mu+
--   u)/2)n_2}$. The ideal weak displacement kernel is $K_{\mu
--   u}(f)=\sum_ns_nf(\Lambda_n)$ on Schwartz tests. With the positive Weyl phase $W(a,b)=e^{(ab^*-a^*b)/2}$, evaluating its Gaussian-smearing convolution gives
--
--   $$K_\Delta(z)=\sum_ns_n\int_{\mathbb C}\frac{e^{-(|b|^2+|\Lambda_n+b-z|^2)/\Delta^2}}{\pi\Delta^2/2}W(-b,z)W(z-b,\Lambda_n+b-z)\,d^2b=\sum_ns_ne^{-|z-\Lambda_n|^2/(2\Delta^2)-\Delta^2|z+\Lambda_n|^2/8}.$$
--
--   This is the actual overlap $\langle w_{\mu,\Delta},D_z w_{
--   u,\Delta}\rangle$ of the smeared comb waves $w_{\mu,\Delta}(x)=\sqrt{2/\sqrt\pi}\sum_{q\in\sqrt\pi(2\mathbb Z+\mu)}e^{-(x-q)^2/(2\Delta^2)-\Delta^2(x+q)^2/8}$. Their computed squared norms $Z_\mu=\|w_{\mu,\Delta}\|_2^2$ are positive. Individually normalized overlaps are $K_\Delta(z)/\sqrt{Z_\mu Z_
--   u}$. Pairings and overlaps are integrable, the weak lattice sums converge, and $\int K_\Delta(z)f(z)d^2z/(2\pi\Delta^2)\to K_{\mu
--   u}(f)$ as $\Delta\downarrow0$. This retains the weak-kernel normalization and avoids treating the finite-smearing Gram matrix as the identity.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 29, Appendix D3 (D8)–(D11): exact GKP displacement kernels

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.29 (D9)--(D11): weak-kernel convolution and true wavefunction overlap;
normalized overlaps divide by computed norms. D8's inconsistent intermediate signs
are not repeated; D9 agrees with the declared positive Weyl convention. -/
theorem gkp_exactSmearing (mu nu : Fin 2) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) (z : ℂ) :
    0 < smearedNorm mu d ∧ 0 < smearedNorm nu d ∧
    Integrable (fun x : ℝ => conj (smearedWave mu d x) * displaceWave z (smearedWave nu d) x) ∧
    smearedKernelIntegral mu nu d z = smearedKernelSum mu nu d z ∧
    (∫ x : ℝ, conj (smearedWave mu d x) * displaceWave z (smearedWave nu d) x) =
      smearedKernelSum mu nu d z ∧
    (∫ x : ℝ, conj (normalizedSmearedWave mu d x) *
      displaceWave z (normalizedSmearedWave nu d) x) =
      smearedKernelSum mu nu d z /
        (Real.sqrt (smearedNorm mu d * smearedNorm nu d) : ℂ) ∧
    (∀ f : SchwartzMap ℂ ℂ,
      Summable (fun n : ℤ × ℤ => kernelPhase mu nu n * f (kernelLattice mu nu n)) ∧
      (∀ e > (0 : ℝ), Integrable (fun a : ℂ => smearedKernelSum mu nu e a * f a)) ∧
      Tendsto (fun e : ℝ => (∫ a : ℂ, smearedKernelSum mu nu e a * f a) /
        (2 * Real.pi * e ^ 2 : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (idealDisplacementKernel mu nu f))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
