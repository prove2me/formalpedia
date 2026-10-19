-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_wernerLowerCertificates
-- name    : QAlgorithms.Papers.Independent.Information100.P04.wernerLowerCertificates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:35:36.355177+00:00
-- url     : https://prove2.me/theorems/889154aa-31d1-45c9-8e3b-45969e5c97b5
-- title:
--   Exact feasible qutrit Werner lower certificates
-- statement:
--   Let $\rho_p$ be the qutrit Werner state of antisymmetric weight $p$. There exist exact rational finite POVMs on the indicated blocks whose norm scores $\ell$, divided by the block length, achieve the following bounds:
--
--   $$E_{d,\mathrm{PPT}}(\rho_{25/26})\ge0.5836,\qquad E_{d,\mathrm{PPT}}(\rho_{3/4})\ge0.144222039901,\qquad E_{d,\mathrm{PPT}}(\rho_{9/10})\ge0.414801754074.$$
--
--   The first certificate uses 48 copies and 49 outcomes; the second uses 48 copies; the third uses 32 copies. Each witness has PSD effects summing to the identity, and the displayed values are lower bounds on its normalized score. These are achievable rates from exact feasible measurements, without a claim of finite-level optimality or of operational upper bounds.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 30, wernerLowerCertificates

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Exact feasible Werner POVM certificates, PDF p.30: these are achievable lower rates,
with the stated block lengths, not finite-level optimality or operational upper bounds. -/
theorem wernerLowerCertificates :
    (∃ M : Measurement ((Fin 48 → Fin 3) × (Fin 48 → Fin 3)), M.outcomes = 49 ∧
      (∀ j, IsRationalMatrix (M.effect j)) ∧
      5836/10000 ≤ ell (copies (werner 3 (25/26)) 48) M.effect / 48) ∧
    (∃ M : Measurement ((Fin 48 → Fin 3) × (Fin 48 → Fin 3)),
      (∀ j, IsRationalMatrix (M.effect j)) ∧
      144222039901/1000000000000 ≤ ell (copies (werner 3 (3/4)) 48) M.effect / 48) ∧
    (∃ M : Measurement ((Fin 32 → Fin 3) × (Fin 32 → Fin 3)),
      (∀ j, IsRationalMatrix (M.effect j)) ∧
      414801754074/1000000000000 ≤ ell (copies (werner 3 (9/10)) 32) M.effect / 32) ∧
    5836/10000 ≤ distillable (werner 3 (25/26)) ∧
    144222039901/1000000000000 ≤ distillable (werner 3 (3/4)) ∧
    414801754074/1000000000000 ≤ distillable (werner 3 (9/10)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
