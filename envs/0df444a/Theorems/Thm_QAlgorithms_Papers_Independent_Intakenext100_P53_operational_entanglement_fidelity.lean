-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_operational_entanglement_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.operational_entanglement_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:26:37.071988+00:00
-- url     : https://prove2.me/theorems/f916a3b6-4ede-449c-af30-8abe5effe248
-- title:
--   Operational entanglement fidelity and its SRM expression
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   For every deterministic POVM $\{\Pi_i\}$ on $AC$, the actual induced port-selection channel has
--   $$F=\frac1{d^2}\sum_i\operatorname{Re}\operatorname{tr}\!\left[\Pi_i(O_A\otimes I_C)\sigma_i(O_A^\dagger\otimes I_C)\right].$$
--   For $O=I$, define $S_i=\rho^{-1/2}\sigma_i\rho^{-1/2}$ with the support inverse square root, and $\Pi_i=S_i+(I-\operatorname{supp}\rho)/N$. These effects form a deterministic POVM, and its operational fidelity equals
--   $$F=\frac1{d^2}\sum_i\operatorname{Re}\operatorname{tr}(\rho^{-1/2}\sigma_i\rho^{-1/2}\sigma_i).$$
--   This identifies the physical teleportation experiment with the signal-operator formula. The missing trace in printed Eq.(6) is restored from Eq.(3) and Appendix C.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 2, II, Eqs.(3)-(6): operational entanglement-fidelity formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.2, Eqs.(3)-(6), p.7: operational fidelity and the SRM trace formula.
The trace missing from printed Eq.(6) is fixed by Eq.(3) and Appendix C. -/
theorem operational_entanglement_fidelity (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    (∀ (O : Op (Ports d N)) (E : Fin N → Op (AC d N)),
      NormalizedResource O → DeterministicPOVM E →
      pbtFidelity O E = (d : ℝ)⁻¹ ^ 2 * ∑ i,
        (Matrix.trace (E i * liftA O * pbtSignal d N i * (liftA O)ᴴ)).re) ∧
    DeterministicPOVM (completedSRM d N) ∧
    pbtFidelity (1 : Op (Ports d N)) (completedSRM d N) =
      (d : ℝ)⁻¹ ^ 2 * ∑ i,
        (Matrix.trace (inverseSqrt (pbtRho d N) * pbtSignal d N i *
          inverseSqrt (pbtRho d N) * pbtSignal d N i)).re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
