-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P38_dephasedOutput_entropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P38.dephasedOutput_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:42:35.375219+00:00
-- url     : https://prove2.me/theorems/57c1a04c-e9fe-4166-91a3-133f06588cc9
-- title:
--   Entropy of the actual dephased channel output
-- statement:
--   Let $d\ge2$, $\Delta\ge1$, and $n\ge1$ be integers. Let $\mathcal M$ be a completely positive trace-preserving map on a $d$-dimensional Hilbert space $H$, and let $\mathcal T$ completely dephase a fixed basis of a $\Delta$-dimensional space $B$. Write $\overline{\mathcal M}=\mathcal M\otimes\mathcal T$, $A=H^{\otimes n}$, and $B_n=B^{\otimes n}$, grouping the original registers before the flags. Let $R$ be a positive semidefinite trace-one operator on $A\otimes B_n$. For a computational flag $\omega$, set $K_\omega=\langle\omega|R|\omega\rangle$ and $\lambda_\omega=\operatorname{Tr}K_\omega$. Define $\rho_\omega=K_\omega/\lambda_\omega$ when $\lambda_\omega>0$, and choose the same fixed unit basis state on $A$ at every zero-weight branch.
--
--   All entropies use base $d$: $S_d(\sigma)=-\operatorname{Tr}(\sigma\log_d\sigma)$ and $H_d(\lambda)=-\sum_\omega\lambda_\omega\log_d\lambda_\omega$, with zero summands equal to zero.
--
--   Then
--
--   $$
--   S_d\!\left(\overline{\mathcal M}^{\otimes n}(R)\right)=H_d(\lambda)+\sum_\omega\lambda_\omega S_d\!\left(\mathcal M^{\otimes n}(\rho_\omega)\right).
--   $$
--
--   This is the block entropy identity for the actual dephased output, retaining the original channel's entropy units.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, PDF p. 4, §II B Eq.(19): entropy of the dephased channel output

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eqs.(19)-(20).
The entropy formula concerns the actual product-channel output, in base d. -/
theorem dephasedOutput_entropy
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R) (a0 : Word n d) :
    entropyD d (dephasedPower M n R) = flagEntropy d R +
      ∑ b : Word n delta, branchWeight R b *
        entropyD d (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P38

end
