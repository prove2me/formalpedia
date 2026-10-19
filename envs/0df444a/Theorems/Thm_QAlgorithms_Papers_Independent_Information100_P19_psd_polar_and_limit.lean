-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_psd_polar_and_limit
-- name    : QAlgorithms.Papers.Independent.Information100.P19.psd_polar_and_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:42:51.771987+00:00
-- url     : https://prove2.me/theorems/188b7d3e-277d-4900-a620-44f48d88973e
-- title:
--   §3 unnumbered: PSD moment duality
-- statement:
--   For degree $n\ge1$, let $M_n^{\rm psd}$ be the closed conic hull of finite nonnegative spectral evaluation vectors. Then
--   $$I_n^{\rm psd}=(M_n^{\rm psd})^\circ.$$
--   The trace-one uniform spectra of increasing ranks converge to the vector which is $1$ on $[1^n]$ and $0$ on every other partition. For $n\ge2$ this vector has no finite trace-one nonnegative spectral realization. The closure is therefore essential.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 12, §3 unnumbered: PSD moment duality

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §3 unnumbered: PSD moment duality; arXiv:2609.29471v1, PDF pp.12. -/
theorem psd_polar_and_limit (n : ℕ) (hn : 1 ≤ n) :
    psdCone n = spectralPolar (psdMom n) ∧
    Tendsto (fun m : ℕ => @spectralMoments n (m+1) (fun _ => 1 / ((m:ℝ)+1)))
      atTop (nhds (fun l : Part n => if ∀ k ∈ l.val, k = 1 then 1 else 0)) ∧
    (2 ≤ n → ¬ ∃ d : ℕ, 0 < d ∧ ∃ x : Fin d → ℝ,
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
      spectralMoments x = (fun l : Part n => if ∀ k ∈ l.val, k=1 then 1 else 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
