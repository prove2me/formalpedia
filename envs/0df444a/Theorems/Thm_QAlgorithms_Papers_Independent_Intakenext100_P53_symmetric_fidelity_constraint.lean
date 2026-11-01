-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_symmetric_fidelity_constraint
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.symmetric_fidelity_constraint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:30:34.359155+00:00
-- url     : https://prove2.me/theorems/35080d14-6923-4aa6-9c3c-0fdcef3a11b0
-- title:
--   Symmetric-port fidelity constraint and finite-port obstruction
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Consider a deterministic protocol with $p_i=1/N$. Let $F_{i|k}$ be the normalized conditional overlap with the reference-$B_k$ singlet following outcome $i$. Suppose $F_{i|i}=F$, where $F$ is the actual port-selection entanglement fidelity, and $F_{i|k}=F_{\mathrm{other}}$ for $i\ne k$. Its coding probabilities and fidelities obey
--   $$q_{i|k}=d^2p_iF_{i|k},\qquad F+(N-1)F_{\mathrm{other}}=\frac N{d^2},\qquad F<1.$$
--   Moreover, if $N\ge2$, $F=1-\epsilon$ and $0<\epsilon<1-d^{-2}$, then
--   $$F_{\mathrm{other}}=\frac1{d^2}-\frac{1-d^{-2}-\epsilon}{N-1}<\frac1{d^2}.$$
--   At $N=1$ the first identity yields $F=d^{-2}$ and does not constrain an unused other-port fidelity. This gives the source's finite-port obstruction in its explicitly symmetric setting.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 5, VI Eqs.(23)-(25): symmetric-port fidelity constraint and finite-N obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF pp.4-5, Eqs.(23)-(25): symmetric physical constraint and finite-N
obstruction. The rearranged equation is restricted to N>=2. -/
theorem symmetric_fidelity_constraint (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (O : Op (Ports d N)) (E : Fin N → Op (AC d N))
    (hO : NormalizedResource O) (hE : DeterministicPOVM E)
    (Fother : ℝ) (hsym : SymmetricPorts O E Fother) :
    (∀ i k, codingProbability O (E i) k =
      (d : ℝ) ^ 2 * pbtBranchProbability O (E i) * conditionalFidelity O (E i) k) ∧
    pbtFidelity O E + ((N : ℝ) - 1) * Fother = (N : ℝ) / (d : ℝ) ^ 2 ∧
    pbtFidelity O E < 1 ∧
    (∀ eps : ℝ, 2 ≤ N → 0 < eps → eps < 1 - (d : ℝ)⁻¹ ^ 2 →
      pbtFidelity O E = 1 - eps →
      Fother = (d : ℝ)⁻¹ ^ 2 - (1 - (d : ℝ)⁻¹ ^ 2 - eps) / ((N : ℝ) - 1) ∧
      Fother < (d : ℝ)⁻¹ ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
