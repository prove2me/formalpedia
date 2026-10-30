-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_standard_pbt_performance
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.standard_pbt_performance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:05:51.412554+00:00
-- url     : https://prove2.me/theorems/1ee0a0d1-ac70-4264-93ab-9a1c79fe23e3
-- title:
--   Exact discrimination success and entanglement fidelity of standard PBT
-- statement:
--   Let $d,N\ge1$ be integers. Write $\Phi^+=|\Phi^+\rangle\langle\Phi^+|$, where $|\Phi^+\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle$, and let $\varphi_0=(\Phi^+)^{\otimes N}$ be the port resource. On $A^N B$, define $\rho_i=\Phi^+_{A_iB}\otimes I_{A_i^c}/d^{N-1}$, $\bar\rho=\sum_i\rho_i$, and $\Pi$ as the support projection of $\bar\rho$. All inverse powers are generalized spectral inverse powers, zero on the kernel. The fixed measurement is
--
--   $$E_i^0=\bar\rho^{-1/2}\rho_i\bar\rho^{-1/2}+\frac{I-\Pi}{N}.$$
--
--   The complementary term completes the PGM to a full POVM without affecting the ensemble probabilities. Let $p(\rho,E)=N^{-1}\sum_i\operatorname{tr}(E_i\rho_i)$. Let $F(\varphi,E)$ denote the entanglement fidelity of deterministic single-input PBT: Alice measures $A_0A^N$ with the $N$-outcome POVM $E$, communicates $i$, and Bob keeps $B_i$ as the output and traces out his other ports. Thus $F=\langle\Phi^+|(\Lambda\otimes\mathrm{id})(\Phi^+)|\Phi^+\rangle$ for the resulting physical channel $\Lambda$.
--
--   For a partition $\mu\vdash_d N$, let $m_\mu=\dim V_\mu^d$ and $d_\mu=\dim W_\mu$ be the Weyl and Specht dimensions. In each inner sum, $\mu=\alpha+\square$ ranges over valid partitions obtained by adding one box. Then
--
--   $$p(\rho,E^0)=\frac1{Nd^N}\sum_{\alpha\vdash_d N-1}\left(\sum_{\mu=\alpha+\square}\sqrt{m_\mu d_\mu}\right)^2,$$
--   $$F(\varphi_0,E^0)=\frac1{d^{N+2}}\sum_{\alpha\vdash_d N-1}\left(\sum_{\mu=\alpha+\square}\sqrt{m_\mu d_\mu}\right)^2.$$
--
--   The square is taken separately for every $\alpha$. These are the exact standard-protocol performance formulas, including $N=1$ and $d=1$.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 8, §4.1, (4.13); §6, (6.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Section 4.1, PDF pp.8-10, (4.13), and p.15, (6.1): exact standard PBT
performance. The inner sum is squared separately for each alpha. -/
theorem standard_pbt_performance (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    discriminationSuccess (portRho d N) (standardPGM d N) =
      coefficientScore (d := d) (N := N) (fun _ => 1) / ((N : ℝ) * (d : ℝ)^N) ∧
    pbtFidelity (standardResource d N) (standardPGM d N) =
      coefficientScore (d := d) (N := N) (fun _ => 1) / (d : ℝ)^(N+2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
