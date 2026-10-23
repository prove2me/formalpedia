-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_dephasing_inputs_maximize_mutual_information
-- name    : QAlgorithms.Papers.Independent.Next46.P40.dephasing_inputs_maximize_mutual_information
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:57:56.008502+00:00
-- url     : https://prove2.me/theorems/07fc06dc-a12f-42b7-960e-dab28046e795
-- title:
--   Diagonal inputs maximize generalized-dephasing EA information
-- statement:
--   Let $A'$ and $B$ have the same finite nonzero basis index set, and let $E$ be finite and nonzero. Choose normalized environmental vectors $|e_i\rangle^E$, which need not be orthogonal. Define the isometry $U|i\rangle=|i\rangle|e_i\rangle$ and the generalized dephasing channel $\mathcal N(X)=\operatorname{Tr}_E UXU^\dagger$. For any normalized purification $\phi^{RA'}$ of an input $\rho$, put $r_i=\langle i|\rho|i\rangle$, $\Delta\rho=\sum_i r_i|i\rangle\langle i|$, and let $\phi_\Delta=\sum_i\sqrt{r_i}|i\rangle|i\rangle$ be its canonical purification. If $\theta=(\mathrm{id}\otimes\mathcal N)\phi$ and $\theta_\Delta=(\mathrm{id}\otimes\mathcal N)\phi_\Delta$, then
--
--   $$I(R;B)_\theta\le I(A;B)_{\theta_\Delta}=2H(r)-H\!\left(\sum_i r_i|e_i\rangle\langle e_i|\right).$$
--
--   All entropies use base two. Thus diagonal inputs suffice for the EA mutual-information optimization. This covers generalized dephasing, including both complete dephasing and the identity channel as special cases.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 12, Appendix C, Lemma 9, (86)–(88)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF p.12, Lemma 9 and (88): dephasing the input can only increase
EA mutual information; the diagonal value is 2H(r)-H(sum r_i phi_i).
Both theta states are channel outputs of explicitly given purifications. -/
theorem dephasing_inputs_maximize_mutual_information
    [Nonempty A] [Nonempty E] [Nonempty R]
    (env : A → EuclideanSpace ℂ E) (henv : ∀ a, ‖env a‖ = 1)
    (v : EuclideanSpace ℂ (R × A)) (hv : ‖v‖ = 1) :
    let rho := traceLeft (pureDensity v)
    let theta := idTensorSuperop (generalizedDephasing env) (pureDensity v)
    let thetaDiag := idTensorSuperop (generalizedDephasing env)
      (pureDensity (diagonalPurification rho))
    mutualInformation theta ≤ mutualInformation thetaDiag ∧
      mutualInformation thetaDiag =
        2 * vnEntropy (diagonalPart rho) -
          vnEntropy (∑ a, ((rho a a).re : ℂ) • pureDensity (env a)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
