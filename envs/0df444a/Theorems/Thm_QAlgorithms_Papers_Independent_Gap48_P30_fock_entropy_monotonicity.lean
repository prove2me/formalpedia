-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_fock_entropy_monotonicity
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.fock_entropy_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:19:02.390518+00:00
-- url     : https://prove2.me/theorems/927ed662-e9e7-442b-8b1b-221e1cc98a13
-- title:
--   Fock-output entanglement monotonicity and vacuum minimum
-- statement:
--   Let $|\Psi_x^{(k)}\rangle$ be the normalized output for a Fock input $|k\rangle$ and vacuum environment, where $0\le x<1$. Its entanglement is the entropy in nats of its squared Schmidt law:
--
--   $$
--   E(|\Psi_x^{(k)}\rangle)=\sum_{n\ge0}-p_n^{(k)}(x)\log p_n^{(k)}(x),
--   \qquad p_n^{(k)}(x)=(1-x^2)^{k+1}x^{2n}\binom{n+k}{n}.
--   $$
--
--   The entropy is interpreted in the extended nonnegative reals with $0\log0=0$. For $r\ge0$ and integers $k\le j$, one has $E(|\Psi_{\tanh r}^{(k)}\rangle)\le E(|\Psi_{\tanh r}^{(j)}\rangle)$. For every $k$ and $0\le r\le s$, one has $E(|\Psi_{\tanh r}^{(k)}\rangle)\le E(|\Psi_{\tanh s}^{(k)}\rangle)$. In particular the vacuum input minimizes the output entanglement among Fock inputs at each fixed $r$.
--
--   The inequalities are non-strict: at $r=0$ all these product outputs have zero entanglement. No analogous ordering by input photon mean is asserted for arbitrary superpositions.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 4, Figure 2; Appendix 4b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.3-4, Figure 2 and Appendix 4b p.7.
The entanglement is nondecreasing in both photon number and squeezing, and
vacuum minimizes it among Fock inputs. At zero squeezing all entropies vanish. -/
theorem fock_entropy_monotonicity :
    (∀ lambda : ℝ, 0 ≤ lambda → lambda < 1 → ∀ k : ℕ,
      squeezingEntanglement (squeezed k lambda) = schmidtEntropy k lambda) ∧
    (∀ r : ℝ, 0 ≤ r → ∀ k j : ℕ, k ≤ j →
      squeezingEntanglement (squeezed k (Real.tanh r)) ≤ squeezingEntanglement (squeezed j (Real.tanh r))) ∧
    (∀ k : ℕ, ∀ r s : ℝ, 0 ≤ r → r ≤ s →
      squeezingEntanglement (squeezed k (Real.tanh r)) ≤ squeezingEntanglement (squeezed k (Real.tanh s))) ∧
    (∀ r : ℝ, 0 ≤ r → ∀ k : ℕ,
      squeezingEntanglement (squeezed 0 (Real.tanh r)) ≤ squeezingEntanglement (squeezed k (Real.tanh r))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
