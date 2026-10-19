-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P47_spectral_common_mub_equivalence
-- name    : QAlgorithms.Papers.Independent.Information100.P47.spectral_common_mub_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:34:19.299337+00:00
-- url     : https://prove2.me/theorems/20594534-2300-4417-b45d-9cc6f085e8a3
-- title:
--   Common-MUB equivalence for spectral distance
-- statement:
--   Let $A=(A_x)_{x=1}^n$ be a POVM on $\mathbb C^d$, with $d,n\ge1$. Fix the computational reference basis. Suppose each effect admits an orthonormal eigenbasis $(\lambda_{i|x})_{i=1}^d$, and there is an orthonormal basis $(v_j)_{j=1}^d$ such that $|\langle\lambda_{i|x},v_j\rangle|=1/\sqrt d$ for every $x,i,j$. Define the spectral distance by $D_\infty(A,B)=\frac12\sum_x\|A_x-B_x\|_{\mathrm{op}}$. Let $C_{D_\infty}(A)$ be its minimum over complete diagonal POVMs with the same labels, let $C_{D_\infty}^{\max}$ maximize this quantity over all simultaneous unitary conjugations, and let $S_{D_\infty}$ minimize the distance over POVMs $(q_x I)_x$ with $q_x\ge0$ and $\sum_xq_x=1$. Then
--
--   $$C_{D_\infty}^{\max}(A)=S_{D_\infty}(A).$$
--
--   This gives a concrete norm-distance equivalence even for noncommuting effects. The common unbiased basis is existential and need not itself be unbiased to the original reference basis.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, PDF p. 6, §III B, Eq. (32)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF pp.5–6, Eq.(32): only the spectral (p=infinity) specialization is asserted. -/
theorem spectral_common_mub_equivalence {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (A : Measurement d n) (hA : IsPOVM A) (hM : CommonMUB A) :
    maxCoherence spectralDistance A = sharpness spectralDistance A := by sorry

end QAlgorithms.Papers.Independent.Information100.P47

end
