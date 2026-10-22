-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P38_purifiedOutput_blockDecomposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P38.purifiedOutput_blockDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:43:03.359812+00:00
-- url     : https://prove2.me/theorems/3600423e-be6c-4864-8312-7ff8f0db7751
-- title:
--   Dephased output on a common purified input
-- statement:
--   Let $d\ge2$, $\Delta\ge1$, and $n\ge1$ be integers. Let $\mathcal M$ be a completely positive trace-preserving map on a $d$-dimensional Hilbert space $H$, and let $\mathcal T$ completely dephase a fixed basis of a $\Delta$-dimensional space $B$. Write $\overline{\mathcal M}=\mathcal M\otimes\mathcal T$, $A=H^{\otimes n}$, and $B_n=B^{\otimes n}$, grouping the original registers before the flags. Let $R$ be a positive semidefinite trace-one operator on $A\otimes B_n$. For a computational flag $\omega$, set $K_\omega=\langle\omega|R|\omega\rangle$ and $\lambda_\omega=\operatorname{Tr}K_\omega$. Define $\rho_\omega=K_\omega/\lambda_\omega$ when $\lambda_\omega>0$, and choose the same fixed unit basis state on $A$ at every zero-weight branch.
--
--   Let $C$ be any finite nonempty reference space, and let $|\psi\rangle\in(A\otimes B_n)\otimes C$ be a unit purification of $R$, so $\operatorname{Tr}_C|\psi\rangle\langle\psi|=R$. Define $|\psi_\omega\rangle=\langle\omega|\psi\rangle/\sqrt{\lambda_\omega}$ for positive weights, using a fixed unit basis vector of $A\otimes C$ otherwise. Write $\Phi=|\psi\rangle\langle\psi|$ and $\Phi_\omega=|\psi_\omega\rangle\langle\psi_\omega|$. These conditional purifications come from the same $\psi$ and the same reference, rather than independent choices.
--
--   After moving the unchanged reference before the flag, the exact identity is
--
--   $$
--   (\overline{\mathcal M}^{\otimes n}\otimes\mathrm{id}_C)(\Phi)=\sum_\omega\lambda_\omega\,(\mathcal M^{\otimes n}\otimes\mathrm{id}_C)(\Phi_\omega)\otimes|\omega\rangle\langle\omega|.
--   $$
--
--   This keeps reference coherences and identifies the common conditional purifications. **Formalization Note** The identity on the reference, suppressed in the printed right side of Eq. (22), is restored as in Eq. (23); the left operator is explicitly reindexed to match the right register order.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, PDF p. 4, §II B Eq.(22): output on a purified input with a dephased flag

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eqs.(21)-(22).
Each conditional purification comes from projection of this same psi.
The printed RHS suppresses id_anc; it is explicitly restored here, as in (23).
The reference and flag are regrouped explicitly on the left. This is a typing
clarification, not an additional communication resource. -/
theorem purifiedOutput_blockDecomposition
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpsi : IsState psi) (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    purifiedOutput M n psi = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (withReference (piSuperop (fun _ : Fin n => M))
          (pureDensity (conditionalPurification a0 c0 R psi b)))
        (pureDensity (ket b)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P38

end
