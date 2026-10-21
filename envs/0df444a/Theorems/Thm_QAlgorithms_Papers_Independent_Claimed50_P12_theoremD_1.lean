-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_theoremD_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.theoremD_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:56:36.494724+00:00
-- url     : https://prove2.me/theorems/ce652c01-44d4-47bc-b23e-d3212cd09449
-- title:
--   k-extendible approximation from squashed entanglement
-- statement:
--   Let $\rho_{AC}$ be a density operator on nonzero finite-dimensional systems, let $k\ge1$, and write $E_{\rm sq}(\rho)=\tfrac12\inf_{\rho_{AEC}}I(A:C|E)$, over all finite ancillary dimensions and extensions of $\rho_{AC}$. There is a $k$-extendible density operator $\omega_{AC}$ with
--
--   $$\Delta(\rho_{AC},\omega_{AC})\le(k-1)\sqrt{\frac{\ln2}{2}E_{\rm sq}(\rho_{AC})}.$$
--
--   The same existence statement holds with purified distance $\sqrt{1-F(\rho,\omega)^2}$ in place of $\Delta$, as specified in footnote 12. The witnesses may be chosen separately. A $k$-extension has the same $A,C_i$ marginal for every $i$.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 27, Theorem D.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Theorem D.1, Eq.206 and footnote 12 (PDF p.27), finite-system setting.
The same bound holds for purified distance; the witnesses may be chosen separately. -/
theorem theoremD_1 {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    [Nonempty A] [Nonempty C] (rho : Op (A × C)) (hrho : IsDensityMatrix rho)
    (k : ℕ) (hk : 0 < k) :
    (∃ omega : Op (A × C), IsDensityMatrix omega ∧ KExtendible k omega ∧
      generalizedTraceDistance rho omega ≤
        ((k : ℝ)-1) * Real.sqrt (Real.log 2 / 2 * squashedEntanglement rho)) ∧
    (∃ omega : Op (A × C), IsDensityMatrix omega ∧ KExtendible k omega ∧
      Real.sqrt (1-rootFidelity rho omega ^ 2) ≤
        ((k : ℝ)-1) * Real.sqrt (Real.log 2 / 2 * squashedEntanglement rho)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
