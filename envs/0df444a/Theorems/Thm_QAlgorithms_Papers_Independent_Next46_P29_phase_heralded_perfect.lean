-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_phase_heralded_perfect
-- name    : QAlgorithms.Papers.Independent.Next46.P29.phase_heralded_perfect
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:22:39.758343+00:00
-- url     : https://prove2.me/theorems/06a282cb-3aa5-4bda-b957-29517e7b7f08
-- title:
--   Heralded phase recovery has success probability N/(N+1)
-- statement:
--   For the uniform number token of cutoff $N\ge0$ and its actual Haar encoding $\mathcal E_N$, measure total number $t$ and accept exactly $1\le t\le N$. Decode the accepted sector by the coherent inverse $|n,b\rangle\mapsto|b\rangle$ for $n+b=t$. The resulting accepted operation $\mathcal R_{\mathrm{acc}}$ is completely positive and trace-nonincreasing, and every qubit density operator satisfies
--
--   $$\mathcal R_{\mathrm{acc}}\mathcal E_N(\rho)=\frac{N}{N+1}\rho,\qquad\operatorname{Tr}\mathcal R_{\mathrm{acc}}\mathcal E_N(\rho)=\frac{N}{N+1}.$$
--
--   This achieved probability is zero at the vacuum cutoff; conditional recovery is not asserted on a nonexistent success event.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 12, §IV.B: heralded phase decoding, Eq.(59)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.12, Eq.(59): the stated measurement achieves heralded exact recovery.
The success probability is zero at `N = 0`; it is not claimed to be optimal. -/
theorem phase_heralded_perfect (N : ℕ) :
    IsSubchannel (phaseAccepted N) ∧
    ∀ rho, IsDensityMatrix rho →
      phaseAccepted N (phaseEncoding N rho) = ((N : ℝ) / (N + 1) : ℂ) • rho ∧
      (phaseAccepted N (phaseEncoding N rho)).trace.re = (N : ℝ) / (N + 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
