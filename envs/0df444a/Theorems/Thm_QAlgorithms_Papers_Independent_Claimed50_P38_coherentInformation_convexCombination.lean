-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P38_coherentInformation_convexCombination
-- name    : QAlgorithms.Papers.Independent.Claimed50.P38.coherentInformation_convexCombination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:44:26.040802+00:00
-- url     : https://prove2.me/theorems/5726b8ca-733f-453a-b5fe-ffd49cb8d8f3
-- title:
--   Exact convex combination of conditional coherent informations
-- statement:
--   Let $d\ge2$, $\Delta\ge1$, and $n\ge1$ be integers. Let $\mathcal M$ be a completely positive trace-preserving map on a $d$-dimensional Hilbert space $H$, and let $\mathcal T$ completely dephase a fixed basis of a $\Delta$-dimensional space $B$. Write $\overline{\mathcal M}=\mathcal M\otimes\mathcal T$, $A=H^{\otimes n}$, and $B_n=B^{\otimes n}$, grouping the original registers before the flags. Let $R$ be a positive semidefinite trace-one operator on $A\otimes B_n$. For a computational flag $\omega$, set $K_\omega=\langle\omega|R|\omega\rangle$ and $\lambda_\omega=\operatorname{Tr}K_\omega$. Define $\rho_\omega=K_\omega/\lambda_\omega$ when $\lambda_\omega>0$, and choose the same fixed unit basis state on $A$ at every zero-weight branch.
--
--   Let $C$ be any finite nonempty reference space, and let $|\psi\rangle\in(A\otimes B_n)\otimes C$ be a unit purification of $R$, so $\operatorname{Tr}_C|\psi\rangle\langle\psi|=R$. Define $|\psi_\omega\rangle=\langle\omega|\psi\rangle/\sqrt{\lambda_\omega}$ for positive weights, using a fixed unit basis vector of $A\otimes C$ otherwise. Write $\Phi=|\psi\rangle\langle\psi|$ and $\Phi_\omega=|\psi_\omega\rangle\langle\psi_\omega|$. These conditional purifications come from the same $\psi$ and the same reference, rather than independent choices.
--
--   All entropies use base $d$: $S_d(\sigma)=-\operatorname{Tr}(\sigma\log_d\sigma)$ and $H_d(\lambda)=-\sum_\omega\lambda_\omega\log_d\lambda_\omega$, with zero summands equal to zero.
--
--   The computed weights are nonnegative and sum to one, and
--
--   $$
--   \begin{aligned}
--   &S_d\!\left(\overline{\mathcal M}^{\otimes n}(R)\right)-S_d\!\left((\overline{\mathcal M}^{\otimes n}\otimes\mathrm{id}_C)(\Phi)\right)\\
--   &\quad=\sum_\omega\lambda_\omega\left[S_d\!\left(\mathcal M^{\otimes n}(\rho_\omega)\right)-S_d\!\left((\mathcal M^{\otimes n}\otimes\mathrm{id}_C)(\Phi_\omega)\right)\right].
--   \end{aligned}
--   $$
--
--   Thus the coherent information is exactly a convex combination of the conditional coherent informations. The equality includes the cancellation of the flag's Shannon entropy; it is stronger than the corresponding maximum upper bound.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, PDF p. 4, §II B Eq.(24): coherent information is a convex combination

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eq.(24) and following
sentence. Coherent information is EXACTLY a convex combination: the weights
are nonnegative and sum to one, and the Shannon terms cancel. -/
theorem coherentInformation_convexCombination
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpsi : IsState psi) (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    (∀ b : Word n delta, 0 ≤ branchWeight R b) ∧
    (∑ b : Word n delta, branchWeight R b = 1) ∧
    entropyD d (dephasedPower M n R) - entropyD d (purifiedOutput M n psi) =
      ∑ b : Word n delta, branchWeight R b *
        (entropyD d (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b)) -
          entropyD d (withReference (piSuperop (fun _ : Fin n => M))
            (pureDensity (conditionalPurification a0 c0 R psi b)))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P38

end
