-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_fully_optimized_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.fully_optimized_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:07:17.109174+00:00
-- url     : https://prove2.me/theorems/2f9c57f2-6e8d-4dd7-846b-33d0d8116e61
-- title:
--   Fully optimized deterministic PBT fidelity is attained by the same standard PGM
-- statement:
--   Let $d,N\ge1$ be integers. Write $\Phi^+=|\Phi^+\rangle\langle\Phi^+|$, where $|\Phi^+\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle$, and let $\varphi_0=(\Phi^+)^{\otimes N}$ be the port resource. On $A^N B$, define $\rho_i=\Phi^+_{A_iB}\otimes I_{A_i^c}/d^{N-1}$, $\bar\rho=\sum_i\rho_i$, and $\Pi$ as the support projection of $\bar\rho$. All inverse powers are generalized spectral inverse powers, zero on the kernel. The fixed measurement is
--
--   $$E_i^0=\bar\rho^{-1/2}\rho_i\bar\rho^{-1/2}+\frac{I-\Pi}{N}.$$
--
--   The complementary term completes the PGM to a full POVM without affecting the ensemble probabilities. Let $p(\rho,E)=N^{-1}\sum_i\operatorname{tr}(E_i\rho_i)$. Let $F(\varphi,E)$ denote the entanglement fidelity of deterministic single-input PBT: Alice measures $A_0A^N$ with the $N$-outcome POVM $E$, communicates $i$, and Bob keeps $B_i$ as the output and traces out his other ports. Thus $F=\langle\Phi^+|(\Lambda\otimes\mathrm{id})(\Phi^+)|\Phi^+\rangle$ for the resulting physical channel $\Lambda$.
--
--   For each partition $\mu\vdash_d N$, let $P_\mu$ be the full physical Schur isotypic projector, $m_{d,\mu}=\dim V_\mu^d$, and $d_\mu=\dim W_\mu$. A coefficient family $c=(c_\mu)$ is feasible when
--
--   $$c_\mu\ge0,\qquad\sum_{\mu\vdash_d N}c_\mu d_\mu m_{d,\mu}=d^N.$$
--
--   Define $O_c=\sum_\mu\sqrt{c_\mu}P_\mu$, $|\varphi_c\rangle=(O_c\otimes I)|\Phi^+\rangle^{\otimes N}$, and $\varphi_c=|\varphi_c\rangle\langle\varphi_c|$. Feasibility makes this a density operator. Its discrimination ensemble is $\eta_i^c=(O_c\otimes I_B)\rho_i(O_c\otimes I_B)^\dagger$.
--
--   Let $F_{\mathrm{opt}}(d,N)$ be the maximum of the actual physical-channel entanglement fidelity $F(\varphi,E)$ over all density operators $\varphi$ on $A^NB^N$ and all $N$-outcome POVMs $E$ on $A_0A^N$. Then
--
--   $$F_{\mathrm{opt}}(d,N)=\frac1{d^{N+2}}\max_{c\ \mathrm{feasible}}\sum_{\alpha\vdash_d N-1}\left(\sum_{\mu=\alpha+\square}\sqrt{c_\mu d_\mu m_{d,\mu}}\right)^2.$$
--
--   Both maxima are attained: there exists a feasible maximizing $c^*$ such that $F(\varphi_{c^*},E^0)$ equals this common value. The same fixed original PGM therefore attains the optimum over arbitrary mixed resource states and measurements. Symmetry or canonical form is not imposed on a competing protocol.
--
--   **Formalization Note** Lean expresses attainment directly by a feasible maximizer, its fidelity equality, and universal upper bounds over feasible coefficient families and all physical protocols. No real supremum of a potentially empty set is used.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 12, §5, (5.8)-(5.9); §6, (6.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Sections 5-6, PDF pp.12-16, (5.8)-(5.9) and (6.3), together with the
abstract's common-measurement claim. An attained coefficient maximum equals
an attained physical-channel maximum over ALL mixed port resources and POVMs.
The symmetry reduction is conclusion/proof content, never a hypothesis on a
competing protocol. The original PGM is fixed independently of the maximizer. -/
theorem fully_optimized_fidelity (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    IsPOVM (standardPGM d N) ∧
    ∃ c : Schur.Partition d N → ℝ, FeasibleWeights c ∧
      IsDensityMatrix (canonicalResource c) ∧
      pbtFidelity (canonicalResource c) (standardPGM d N) =
        coefficientScore c / (d : ℝ)^(N+2) ∧
      (∀ cprime : Schur.Partition d N → ℝ, FeasibleWeights cprime →
        coefficientScore cprime ≤ coefficientScore c) ∧
      (∀ phi : Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ,
        IsDensityMatrix phi →
        ∀ E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ,
          IsPOVM E → pbtFidelity phi E ≤ coefficientScore c / (d : ℝ)^(N+2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
