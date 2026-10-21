-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_ea_coding_with_input_preservation_and_restoration
-- name    : QAlgorithms.Papers.Independent.Next46.P40.ea_coding_with_input_preservation_and_restoration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:53:39.204801+00:00
-- url     : https://prove2.me/theorems/7b25d87b-a18f-452b-8082-9efe6af3bb7e
-- title:
--   EA coding with exact input preservation and full restoration
-- statement:
--   Fix a CPTP channel $\mathcal N:A'\to B$, an isometric dilation $U:A'\to BE$, and a normalized pure shared resource $|\phi\rangle^{A'R}$, where $R$ is held by the receiver. Put $\rho=\operatorname{Tr}_R\phi$ and $\theta=(\mathcal N\otimes\mathrm{id}_R)(\phi)$. For every $\epsilon,\delta>0$, all sufficiently large positive $n$ admit an integer $M\ge1$, one family of unitary encoders $V_k$ on $A'^n$, and one receiver instrument $\{\mathcal D_k\}$ on $B^nR^n$, chosen before the message, such that
--
--   $$\log_2 M\ge n\bigl(I(R;B)_\theta-\delta\bigr).$$
--
--   For every message $k$, decoding succeeds with probability at least $1-\epsilon$, the input is preserved exactly, $V_k\rho^{\otimes n}V_k^\dagger=\rho^{\otimes n}$, and the nonselective decoder tensored with $\mathrm{id}_{E^n}$ restores the complete unencoded dilation output within full trace norm $\epsilon$.
--
--   The resource is exactly $\phi^{\otimes n}$. This result strengthens ordinary EA communication by preserving the channel input and restoring its joint state with the inaccessible environment.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 5, Theorem 5; code conditions on p.4

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

/-- PDF p.5, Theorem 5, with all three code conditions from p.4.
The channel, pure resource, and its dilation are fixed before error, slack,
blocklength, and code. Integer message counts encode the arbitrarily slackened rate. -/
theorem ea_coding_with_input_preservation_and_restoration
    [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (N : Superop A B) (hN : IsChannel N)
    (U : Matrix (B × E) A ℂ) (hU : Uᴴ * U = 1)
    (hdilation : ∀ X, traceRight (conjSuperop U X) = N X)
    (v : EuclideanSpace ℂ (A × R)) (hv : ‖v‖ = 1) :
    ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
        ∃ m : ℕ, 0 < m ∧ ∃ code : SingleEACode A B R n m,
          (n : ℝ) * (mutualInformation (leftTensor N (pureDensity v)) - delta) ≤
            Real.logb 2 (m : ℝ) ∧ singleEACorrect U v code eps := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
