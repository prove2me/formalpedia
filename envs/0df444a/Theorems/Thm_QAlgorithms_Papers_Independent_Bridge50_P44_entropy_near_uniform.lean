-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_entropy_near_uniform
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.entropy_near_uniform
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:17:03.772379+00:00
-- url     : https://prove2.me/theorems/0feb55fa-1ba6-47b4-99be-cf655319ca39
-- title:
--   Corollary A.10: lower entropy near uniform
-- statement:
--   Let $\rho_{KE}$ be any density matrix on nonzero finite-dimensional systems, let $d=\dim K$, and let $\rho_E=\operatorname{tr}_K\rho_{KE}$ and $\tau_K=I_K/d$. Put $\varepsilon=D(\rho_{KE},\tau_K\otimes\rho_E)\le1/4$. In natural logarithms,
--
--   $$S(K|E)_\rho\ge(1-8\varepsilon)\log d-2h(2\varepsilon).$$
--
--   Here $h$ is binary entropy with $0\log0=0$. No classicality of $K$ is assumed. The result translates closeness to a uniform independent first system into a conditional-entropy lower bound.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 44, Corollary A.10: lower entropy near uniform

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

/-- PDF p.44, Corollary A.10: conditional entropy near a uniform first marginal.
No classicality hypothesis is imposed; the E factor is the actual partial trace. -/
theorem entropy_near_uniform {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (rho : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ)
    (hdistance : traceDistance rho (Matrix.kronecker (maximallyMixed d) (traceLeft rho)) = epsilon)
    (hsmall : epsilon ≤ 1 / 4) :
    (1 - 8 * epsilon) * Real.log d - 2 * Real.binEntropy (2 * epsilon) ≤
      conditionalEntropyNats rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
