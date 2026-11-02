-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_kNonEntangling_compression
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.kNonEntangling_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:42:12.68917+00:00
-- url     : https://prove2.me/theorems/8e93a5d9-0cca-4f40-a6c5-3092cb818762
-- title:
--   Lemma 18: compressed Choi criterion for k-non-entangling maps
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $1\le k\le d$ and let $\Lambda$ be a CP endomap on $d\times d$. A $k$-dimensional projection means a rectangular coisometry $P:\mathbb C^d\to\mathbb C^k$, with $PP^\dagger=I_k$. Then
--
--   $$\Lambda\text{ is }k\text{-non-entangling}\ \Longleftrightarrow\ (I_{d^2}\otimes P\otimes Q)J(\Lambda)(I_{d^2}\otimes P\otimes Q)^\dagger\text{ is separable for every such }P,Q.$$
--
--   The output partition groups $A_{\rm out}\mathbb C^k:B_{\rm out}\mathbb C^k$.
--
--   This tests the whole amplified separable cone using coisometries.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 21, Lemma 18

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

/-- Lemma 18, PDF p.21: coisometry compression criterion on the stated
endomap, with the dimensional domain 1<=k<=d made explicit. -/
theorem kNonEntangling_compression {d k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    (L : Superop (Fin d × Fin d) (Fin d × Fin d)) (hcp : CP L) :
    KNE k L ↔ ∀ P Q : Matrix (Fin k) (Fin d) ℂ,
      Coisometry P → Coisometry Q → IsSeparablePositive (compressChoi L P Q) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
