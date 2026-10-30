-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_contraction_sandwich
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.contraction_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:56:54.934995+00:00
-- url     : https://prove2.me/theorems/70358077-548c-4d26-b647-2142689f5067
-- title:
--   Fact 1: contraction sandwich identity
-- statement:
--   Let $d\ge1$, $k\ge1$, and $n=r+2k$ with $r\ge0$. Let $V^{(k)}$ be the product of the $k$ swaps between registers $n-2k+j$ and $n-j+1$, partially transposed on the final registers. Thus each transposed swap equals $dP^+$ for the normalized Bell projector. For every complex operator $X$ on the first $n-k$ registers,
--
--   $$
--   V^{(k)}(X\otimes I_k)V^{(k)}=(\operatorname{Tr}_{n-2k+1,\ldots,n-k}X\otimes I_{2k})V^{(k)}.
--   $$
--
--   The partial trace is unnormalized. The identity applies to arbitrary operators, including non-Hermitian ones, and is the contraction rule used in subsequent trace calculations.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 9, Fact 1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Fact 1, with n=r+2k: the contraction sandwich identity for every complex
operator X, without positivity or state normalization (PDF pp.9-11, (38)). -/
theorem contraction_sandwich (d r k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (X : Matrix ((Fin r → Fin d) × (Fin k → Fin d)) ((Fin r → Fin d) × (Fin k → Fin d)) ℂ) :
    pairedContraction d r k * liftInput X * pairedContraction d r k =
      liftSurvivor (k := k) (QAlgorithms.traceRight X) * pairedContraction d r k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
