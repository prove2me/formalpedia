-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_compression_partial_trace
-- name    : QAlgorithms.Papers.Independent.Support21.P17.compression_partial_trace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:48:42.601168+00:00
-- url     : https://prove2.me/theorems/af620e4d-ef81-4b61-93cf-3029ca9bd750
-- title:
--   Compression and partial trace identity
-- statement:
--   For positive integers $m,n$, use the constructed tracial dilation $V_{m,n}:\mathbb C^n\to\mathbb C^m\otimes\mathbb C^n\otimes\mathbb C^m$, whose entries are $V_{i,\mu j;\nu}=m^{-1/2}\delta_{ij}\delta_{\mu\nu}$. For arbitrary complex matrices $A\in M_m$ and $B\in M_n\otimes M_m$,
--
--   $$V_{m,n}^*(A\otimes B)V_{m,n}=\frac1m\operatorname{Tr}_{\mathbb C^m}[(I_n\otimes A^{\mathsf T})B].$$
--
--   No positivity or Hermiticity is required. This identity explains the inverse RN-coordinate formula, including the transpose and its normalization.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 15, Lemma 5.2: compression and partial trace identity

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Lemma 5.2, PDF p.15: the constructed compression is partial trace with transpose
and factor 1/m, for arbitrary complex A and B. -/
theorem compression_partial_trace (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (A : M m) (B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (tracialV m n).conjTranspose * Matrix.kronecker A B * tracialV m n =
      (m : ℂ)⁻¹ • traceRight (Matrix.kronecker (1 : M n) A.transpose * B) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
