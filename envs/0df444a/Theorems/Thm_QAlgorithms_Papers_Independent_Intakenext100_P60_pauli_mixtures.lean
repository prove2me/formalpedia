-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_pauli_mixtures
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.pauli_mixtures
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:53:48.819927+00:00
-- url     : https://prove2.me/theorems/9983b557-a677-4027-b2d7-61c65291d5f7
-- title:
--   Example 5: formation and cost for all mixtures of the two Pauli-dilation vectors
-- statement:
--   Let $p_0,p_x,p_y,p_z\ge0$ sum to one, with
--   $$p_0+p_z-p_x-p_y\ge |p_0+p_y-p_x-p_z|,\qquad p_0+p_z-p_x-p_y\ge |p_0+p_x-p_y-p_z|.$$
--   In output:environment order on $\mathbb C^2\otimes\mathbb C^4$, put
--   $$u=\sqrt{p_0}|00\rangle+\sqrt{p_x}|1x\rangle+i\sqrt{p_y}|1y\rangle+\sqrt{p_z}|0z\rangle,$$
--   $$v=\sqrt{p_0}|10\rangle+\sqrt{p_x}|0x\rangle-i\sqrt{p_y}|0y\rangle-\sqrt{p_z}|1z\rangle.$$
--   Write $\rho_s=s|u\rangle\langle u|+(1-s)|v\rangle\langle v|$ for $0\le s\le1$, $\rho_T=\rho_{1/2}$, and $h=H_2(p_0+p_z)$, where $H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ and $0\log_2 0=0$. Entanglement is measured across the two displayed parties.
--
--   For every $s\in[0,1]$,
--   $$E_c(\rho_s)=E_f(\rho_s)=h.$$
--   Moreover, for each positive integer $n$, form the $2^n$ tensor-word projectors from $|u\rangle\langle u|$ and $|v\rangle\langle v|$. Every convex mixture of these projectors has formation $nh$, across all output qubits versus all environments. This assertion does not include arbitrary entangled superpositions of the words.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 9, Example 5: formation and cost for all mixtures of the two Pauli-dilation vectors

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF pp.8--9, Example 5 and (14): cost and formation for every mixture,
plus optimality of every convex mixture of the named positive-length tensor words. -/
theorem pauli_mixtures (p : Fin 4 → ℝ) (hp : PauliAdmissible p) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      formationCostBits (pauliMixture p s) = binEntropy2 (p 0 + p 3) ∧
      formation (pauliMixture p s) = binEntropy2 (p 0 + p 3)) ∧
    (∀ n : ℕ, 0 < n → ∀ mu : (Fin n → Fin 2) → ℝ,
      (∀ w, 0 ≤ mu w) → (∑ w, mu w) = 1 →
      formation (pauliWordMixture p n mu) = n * binEntropy2 (p 0 + p 3)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
