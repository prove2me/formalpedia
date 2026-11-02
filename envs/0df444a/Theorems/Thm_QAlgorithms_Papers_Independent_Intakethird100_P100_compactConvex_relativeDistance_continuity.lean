-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_compactConvex_relativeDistance_continuity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.compactConvex_relativeDistance_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:24:52.73653+00:00
-- url     : https://prove2.me/theorems/467d835b-c3b6-47be-96fe-503e076016a4
-- title:
--   Continuity of distance to a compact convex state set
-- statement:
--   Let $H$ be a complex Hilbert space of arbitrary positive finite dimension $N$. Let $D$ be a compact, real-convex set of density matrices containing $I/N$. Define $E_D(\omega)=\inf_{\tau\in D}S(\omega\Vert\tau)$, where the relative entropy is infinite if $\operatorname{supp}\omega\not\subseteq\operatorname{supp}\tau$.
--
--   All logarithms are natural. States are positive semidefinite matrices of trace one, and the distance $t=\|\sigma-\rho\|_1$ uses the full trace norm, without a factor of one half. Set $\eta(t)=-t\log t$, with $\eta(0)=0$.
--
--   For any density matrices $\sigma,\rho$ with $t\leq 1/3$, the values $E_D(\sigma),E_D(\rho)$ are finite and
--
--   $$
--   |E_D(\sigma)-E_D(\rho)|\leq 2\bigl(t\log N+\eta(t)\bigr)+4t.
--   $$
--
--   This bound applies to a general compact convex state set, without requiring a bipartite system.
--
--   **Formalization Note** The accepted entropy infimum is stored in bits. The Lean bound multiplies its absolute real difference by $\log 2$, which gives exactly the natural-logarithm quantity displayed above.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 2, Theorem, equation (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P100

noncomputable section

open Filter

open scoped ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P100

open QAlgorithms.Papers.Independent.Dependency50.P15
  (relativeDistance relativeDistanceValue positiveOperatorRelativeEntropyBits groupedTensorPower)

open QAlgorithms.Papers.Independent.Information100.P54
  (relativeEntropyBits relativeEntanglement)

/-- Theorem (3), PDF pp.2–3: continuity for every compact real-convex
set of normalized states containing I/N, in arbitrary positive finite dimension.
Finiteness is asserted, rather than assumed before taking real differences. -/
theorem compactConvex_relativeDistance_continuity
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (D : Set (Matrix I I ℂ))
    (hstates : ∀ rho ∈ D, IsDensityMatrix rho)
    (hcompact : IsCompact D) (hconvex : Convex ℝ D)
    (hmixed : (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) ∈ D)
    (sigmaOne sigmaTwo : Matrix I I ℂ)
    (hOne : IsDensityMatrix sigmaOne) (hTwo : IsDensityMatrix sigmaTwo)
    (hclose : traceNorm (sigmaOne - sigmaTwo) ≤ 1 / 3) :
    0 ≤ relativeDistance D sigmaOne ∧ relativeDistance D sigmaOne < ⊤ ∧
    0 ≤ relativeDistance D sigmaTwo ∧ relativeDistance D sigmaTwo < ⊤ ∧
    Real.log 2 * |relativeDistanceValue D sigmaOne - relativeDistanceValue D sigmaTwo| ≤
      2 * (traceNorm (sigmaOne - sigmaTwo) * Real.log (Fintype.card I) +
        Real.negMulLog (traceNorm (sigmaOne - sigmaTwo))) +
      4 * traceNorm (sigmaOne - sigmaTwo) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
