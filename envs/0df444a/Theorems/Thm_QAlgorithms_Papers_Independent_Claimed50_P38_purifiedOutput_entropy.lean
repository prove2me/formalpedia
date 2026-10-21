-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P38_purifiedOutput_entropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P38.purifiedOutput_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:43:41.797752+00:00
-- url     : https://prove2.me/theorems/a2c35b3d-0ba1-49c2-b97b-68becd7105f7
-- title:
--   Entropy of the dephased output with its reference
-- statement:
--   Let $d\ge2$, $\Delta\ge1$, and $n\ge1$ be integers. Let $\mathcal M$ be a completely positive trace-preserving map on a $d$-dimensional Hilbert space $H$, and let $\mathcal T$ completely dephase a fixed basis of a $\Delta$-dimensional space $B$. Write $\overline{\mathcal M}=\mathcal M\otimes\mathcal T$, $A=H^{\otimes n}$, and $B_n=B^{\otimes n}$, grouping the original registers before the flags. Let $R$ be a positive semidefinite trace-one operator on $A\otimes B_n$. For a computational flag $\omega$, set $K_\omega=\langle\omega|R|\omega\rangle$ and $\lambda_\omega=\operatorname{Tr}K_\omega$. Define $\rho_\omega=K_\omega/\lambda_\omega$ when $\lambda_\omega>0$, and choose the same fixed unit basis state on $A$ at every zero-weight branch.
--
--   Let $C$ be any finite nonempty reference space, and let $|\psi\rangle\in(A\otimes B_n)\otimes C$ be a unit purification of $R$, so $\operatorname{Tr}_C|\psi\rangle\langle\psi|=R$. Define $|\psi_\omega\rangle=\langle\omega|\psi\rangle/\sqrt{\lambda_\omega}$ for positive weights, using a fixed unit basis vector of $A\otimes C$ otherwise. Write $\Phi=|\psi\rangle\langle\psi|$ and $\Phi_\omega=|\psi_\omega\rangle\langle\psi_\omega|$. These conditional purifications come from the same $\psi$ and the same reference, rather than independent choices.
--
--   All entropies use base $d$: $S_d(\sigma)=-\operatorname{Tr}(\sigma\log_d\sigma)$ and $H_d(\lambda)=-\sum_\omega\lambda_\omega\log_d\lambda_\omega$, with zero summands equal to zero.
--
--   Then
--
--   $$
--   S_d\!\left((\overline{\mathcal M}^{\otimes n}\otimes\mathrm{id}_C)(\Phi)\right)=H_d(\lambda)+\sum_\omega\lambda_\omega S_d\!\left((\mathcal M^{\otimes n}\otimes\mathrm{id}_C)(\Phi_\omega)\right).
--   $$
--
--   This is the entropy decomposition with the reference preserved, using the same weights as the unpurified input.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, PDF p. 4, §II B Eq.(23): entropy of the output on a purified input

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eq.(23).
The unchanged reference occurs on both sides. All entropies have base d. -/
theorem purifiedOutput_entropy
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpsi : IsState psi) (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    entropyD d (purifiedOutput M n psi) = flagEntropy d R +
      ∑ b : Word n delta, branchWeight R b *
        entropyD d (withReference (piSuperop (fun _ : Fin n => M))
          (pureDensity (conditionalPurification a0 c0 R psi b))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P38

end
