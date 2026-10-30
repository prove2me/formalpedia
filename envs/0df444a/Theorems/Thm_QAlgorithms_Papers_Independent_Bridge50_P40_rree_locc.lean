-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_rree_locc
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.rree_locc
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:04:50.376418+00:00
-- url     : https://prove2.me/theorems/cecf183e-289e-4771-bd5f-cfca690c9116
-- title:
--   LOCC monotonicity of Petz RREE (Vedral et al.)
-- statement:
--   All registers are finite and nonempty, all source kets have unit norm, all density operators are positive semidefinite with trace one, logarithms are base two, and F denotes root fidelity. For any density operator $\rho^{AB}$, any actual finite adaptive LOCC channel $\mathcal M:A:B\to C:D$, and $0\le a\le2$,
--
--   $$E_{\rm RE}^{(a)}(C:D)_{\mathcal M(\rho)}\le E_{\rm RE}^{(a)}(A:B)_\rho.$$
--
--   Here $E_{\rm RE}^{(a)}$ is the infimum of support-aware Petz divergence over separable density operators, with the Umegaki limit at one and the support projection at zero. No fixed bound on the number of local rounds is imposed.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 5, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Lemma 2 (Vedral et al. [21]): the stated Petz RREE is
nonincreasing under actual LOCC. Cited attribution is preserved; it does not
constitute a reason to omit an otherwise fully expressible statement. -/
theorem rree_locc {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (M : Superop (A × B) (C × D)) (hM : IsLOCC M) :
    rree a (M rho) ≤ rree a rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
