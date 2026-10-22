-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P38_dephasedOutput_blockDecomposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P38.dephasedOutput_blockDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:41:55.165698+00:00
-- url     : https://prove2.me/theorems/e766dda9-e009-46be-8ddc-23d3fa5aff50
-- title:
--   The actual dephased output is a sum of computed conditional blocks
-- statement:
--   Let $d\ge2$, $\Delta\ge1$, and $n\ge1$ be integers. Let $\mathcal M$ be a completely positive trace-preserving map on a $d$-dimensional Hilbert space $H$, and let $\mathcal T$ completely dephase a fixed basis of a $\Delta$-dimensional space $B$. Write $\overline{\mathcal M}=\mathcal M\otimes\mathcal T$, $A=H^{\otimes n}$, and $B_n=B^{\otimes n}$, grouping the original registers before the flags. Let $R$ be a positive semidefinite trace-one operator on $A\otimes B_n$. For a computational flag $\omega$, set $K_\omega=\langle\omega|R|\omega\rangle$ and $\lambda_\omega=\operatorname{Tr}K_\omega$. Define $\rho_\omega=K_\omega/\lambda_\omega$ when $\lambda_\omega>0$, and choose the same fixed unit basis state on $A$ at every zero-weight branch.
--
--   The actual product-channel output satisfies
--
--   $$
--   \overline{\mathcal M}^{\otimes n}(R)=\sum_\omega\lambda_\omega\,\mathcal M^{\otimes n}(\rho_\omega)\otimes|\omega\rangle\langle\omega|.
--   $$
--
--   This expresses the output in its flag-diagonal blocks. The weights and conditional inputs are calculated from the supplied input; no decomposition is assumed.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, PDF p. 4, §II B Eq.(17): block diagonal output of a channel with dephasing

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eqs.(17)-(18).
Every conditional input and weight is computed from R. No conditional block
or output decomposition is a hypothesis. The arbitrary a0 only selects a
normalized state on zero-probability branches. -/
theorem dephasedOutput_blockDecomposition
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R) (a0 : Word n d) :
    dephasedPower M n R = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b))
        (pureDensity (ket b)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P38

end
