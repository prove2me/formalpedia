-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_werner_compressions
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.werner_compressions
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:42:54.093526+00:00
-- url     : https://prove2.me/theorems/10869462-7ba6-42b3-8d73-1189081f445e
-- title:
--   Lemma 19: separability threshold for compressed Werner states
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $2\le k<d$ and $-(d+1)\le\beta\le d-1$. Write $F_d$ for the swap operator and
--
--   $$\rho_d(\beta)=\frac{I_{d^2}-\frac{\beta+1}{d}F_d}{d^2-(\beta+1)}.$$
--
--   Then $(P\otimes Q)\rho_d(\beta)(P\otimes Q)^\dagger$ belongs to the separable positive cone for every pair of coisometries $P,Q:\mathbb C^d\to\mathbb C^k$ if and only if
--
--   $$\beta\le\frac{d-k}{k}.$$
--
--   Compressed operators need not be normalized and may be zero.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 21, Lemma 19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Lemma 19, PDF pp.21-22: all coisometry compressions of the Werner
state are separable exactly at the stated threshold. Outputs are not normalized. -/
theorem werner_compressions {k d : ℕ} (hk : 2 ≤ k) (hkd : k < d)
    (beta : ℝ) (hlo : -((d : ℝ) + 1) ≤ beta) (hhi : beta ≤ (d : ℝ) - 1) :
    (∀ P Q : Matrix (Fin k) (Fin d) ℂ, Coisometry P → Coisometry Q →
      IsSeparablePositive (localCoisometryCompression P Q (betaWernerState d beta))) ↔
        beta ≤ ((d : ℝ) - k) / k := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
