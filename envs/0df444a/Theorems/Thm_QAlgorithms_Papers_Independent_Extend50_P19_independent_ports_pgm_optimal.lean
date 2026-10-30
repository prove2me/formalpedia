-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_independent_ports_pgm_optimal
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.independent_ports_pgm_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:03:14.283238+00:00
-- url     : https://prove2.me/theorems/57a848d6-4dc4-4eaf-adfc-f6a439e771bc
-- title:
--   The standard pretty good measurement is optimal for independent maximally entangled ports
-- statement:
--   Let $d,N\ge1$ be integers. Write $\Phi^+=|\Phi^+\rangle\langle\Phi^+|$, where $|\Phi^+\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle$, and let $\varphi_0=(\Phi^+)^{\otimes N}$ be the port resource. On $A^N B$, define $\rho_i=\Phi^+_{A_iB}\otimes I_{A_i^c}/d^{N-1}$, $\bar\rho=\sum_i\rho_i$, and $\Pi$ as the support projection of $\bar\rho$. All inverse powers are generalized spectral inverse powers, zero on the kernel. The fixed measurement is
--
--   $$E_i^0=\bar\rho^{-1/2}\rho_i\bar\rho^{-1/2}+\frac{I-\Pi}{N}.$$
--
--   The complementary term completes the PGM to a full POVM without affecting the ensemble probabilities. Let $p(\rho,E)=N^{-1}\sum_i\operatorname{tr}(E_i\rho_i)$. Let $F(\varphi,E)$ denote the entanglement fidelity of deterministic single-input PBT: Alice measures $A_0A^N$ with the $N$-outcome POVM $E$, communicates $i$, and Bob keeps $B_i$ as the output and traces out his other ports. Thus $F=\langle\Phi^+|(\Lambda\otimes\mathrm{id})(\Phi^+)|\Phi^+\rangle$ for the resulting physical channel $\Lambda$.
--
--   Then $E^0$ is a POVM, and every $N$-outcome POVM $E$ satisfies
--
--   $$p(\rho,E)\le p(\rho,E^0),\qquad F(\varphi_0,E)\le F(\varphi_0,E^0).$$
--
--   This establishes optimality of the standard measurement for every local dimension and positive number of ports.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 11, §4.2, conclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Section 4.2, PDF pp.10-11: the original PGM is an optimal measurement for
independent maximally entangled ports. Both discrimination success and the
physical deterministic PBT entanglement fidelity are maximized. No dual
feasibility condition is a hypothesis. -/
theorem independent_ports_pgm_optimal (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    IsPOVM (standardPGM d N) ∧
    ∀ E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ,
      IsPOVM E →
      discriminationSuccess (portRho d N) E ≤
        discriminationSuccess (portRho d N) (standardPGM d N) ∧
      pbtFidelity (standardResource d N) E ≤
        pbtFidelity (standardResource d N) (standardPGM d N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
