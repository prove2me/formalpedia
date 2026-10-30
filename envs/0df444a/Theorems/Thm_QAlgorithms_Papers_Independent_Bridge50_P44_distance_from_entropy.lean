-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_distance_from_entropy
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.distance_from_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:17:39.583128+00:00
-- url     : https://prove2.me/theorems/7495f8d7-c379-4344-a6a4-a195d106689f
-- title:
--   Lemma A.11: distance from entropy deficiency
-- statement:
--   For any density matrix $\rho_{KE}$ on nonzero finite-dimensional systems, write $d=\dim K$, $\rho_E=\operatorname{tr}_K\rho_{KE}$, and $\tau_K=I_K/d$. With natural-log conditional entropy,
--
--   $$D(\rho_{KE},\tau_K\otimes\rho_E)\le\sqrt{\tfrac12\bigl(\log d-S(K|E)_\rho\bigr)}.$$
--
--   There is no small-distance or classical-key restriction. Nonnegativity of the entropy deficiency is a consequence, rather than a supplied hypothesis. This is the entropy-deficiency estimate used for the upper half of the final entropy bounds.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 44, Lemma A.11: distance from entropy deficiency

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

/-- PDF p.44, Lemma A.11: natural-log entropy deficiency controls distance.
The nonnegativity of the deficiency is derived, never a supplied certificate. -/
theorem distance_from_entropy {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (rho : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (hrho : IsDensityMatrix rho) :
    traceDistance rho (Matrix.kronecker (maximallyMixed d) (traceLeft rho)) ≤
      Real.sqrt ((1 / 2 : ℝ) * (Real.log d - conditionalEntropyNats rho)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
