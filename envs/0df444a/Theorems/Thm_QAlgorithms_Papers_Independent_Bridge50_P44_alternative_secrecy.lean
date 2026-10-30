-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_alternative_secrecy
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.alternative_secrecy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:19:12.346372+00:00
-- url     : https://prove2.me/theorems/4976ec66-f55e-4368-b823-039c6f9f4dc9
-- title:
--   Appendix B: factor-two equivalence
-- statement:
--   Let $K$ be a nonzero finite-dimensional system of dimension $d$, $E$ an arbitrary separable memory, and $\rho_{KE}$ a normalized positive trace-class state. Write $\rho_E=\operatorname{tr}_K\rho_{KE}$, $\tau_K=I_K/d$, and $s=\inf_{\sigma_E}D(\rho_{KE},\tau_K\otimes\sigma_E)$, where every reference $\sigma_E$ is a normalized positive trace-class state. Then
--
--   $$D(\rho_{KE},\tau_K\otimes\rho_E)\le2s\le2D(\rho_{KE},\tau_K\otimes\rho_E).$$
--
--   No optimal-reference attainment is claimed for infinite-dimensional memory. All distances are finite on these states; the infimum is over a nonempty feasible set and is represented in the extended nonnegative reals. The inequality can be multiplied by the same success probability on both sides. It asserts factor-two equivalence, without a composable additivity claim for the optimized criterion.
--
--   If E is finite-dimensional, there exists a normalized reference state attaining s, so the infimum is the minimum printed by the source. The unrestricted separable-memory inequalities remain as stated.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 45, Appendix B: factor-two equivalence

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

/-- PDF pp.44--45, Appendix B: factor-two equivalence with optimized reference
states, on arbitrary separable memory. The infimum is explicitly attained for
finite-dimensional memory, retaining the source's minimum. No infinite-dimensional
compactness or attainment is assumed. Both factors are normalized references;
an abort-success weight multiplies both identically. -/
theorem alternative_secrecy {d : ℕ} (hd : 0 < d) {E : Type} [Countable E]
    (rho : State (Fin d × E)) :
    nuclearDistance rho.coefficients (uniformReference (partialTraceFirst rho.coefficients)) ≤
      2 * optimizedSecrecy rho ∧
    2 * optimizedSecrecy rho ≤
      2 * nuclearDistance rho.coefficients (uniformReference (partialTraceFirst rho.coefficients)) ∧
    (Finite E → ∃ sigma : State E,
      nuclearDistance rho.coefficients (uniformReference sigma.coefficients) =
        optimizedSecrecy rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
