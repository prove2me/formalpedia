-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_entropy_sandwich
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.entropy_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:18:21.785991+00:00
-- url     : https://prove2.me/theorems/dca721b8-2717-476d-8867-ac7bea360eb8
-- title:
--   A.4.2: combined entropy bounds
-- statement:
--   Let $\rho_{KE}$ be a density matrix on nonzero finite-dimensional systems, $d=\dim K$, $\rho_E=\operatorname{tr}_K\rho_{KE}$, $\tau_K=I_K/d$, and $\varepsilon=D(\rho_{KE},\tau_K\otimes\rho_E)\le1/4$. In natural logarithms,
--
--   $$(1-8\varepsilon)\log d-2h(2\varepsilon)\le S(K|E)_\rho\le\log d-2\varepsilon^2.$$
--
--   Here $h$ is the binary entropy. The small-distance domain is inherited from Corollary A.10; the upper estimate alone holds globally. Both displayed bounds are retained as conclusions.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 44, A.4.2: combined entropy bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.44, final display of Appendix A.4.2: both entropy bounds together.
The lower bound inherits epsilon ≤ 1/4 from Corollary A.10. -/
theorem entropy_sandwich {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (rho : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ)
    (hdistance : traceDistance rho (Matrix.kronecker (maximallyMixed d) (traceLeft rho)) = epsilon)
    (hsmall : epsilon ≤ 1 / 4) :
    (1 - 8 * epsilon) * Real.log d - 2 * Real.binEntropy (2 * epsilon) ≤
      conditionalEntropyNats rho ∧
    conditionalEntropyNats rho ≤ Real.log d - 2 * epsilon ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
