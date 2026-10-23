-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_unitalAntidegraderFeasibility
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.unitalAntidegraderFeasibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:52:39.198426+00:00
-- url     : https://prove2.me/theorems/d8132b41-19d7-483b-a49b-48d741331a86
-- title:
--   B.3: unital-qubit antidegrader feasibility (94)–(98)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\sigma_0=I$ and $\sigma_1,\sigma_2,\sigma_3=X,Y,Z$. For real amplitudes $a_k\ge0$ with $\sum_{k=0}^3a_k^2=1$, put $P_a(\rho)=\sum_{k=0}^3 a_k^2\sigma_k\rho\sigma_k$ and $\lambda_k=a_0^2+a_k^2-a_i^2-a_j^2$, where $\{i,j,k\}=\{1,2,3\}$.
--
--   For real triples $x,y$, let
--   $$Y(x,y)=\begin{pmatrix}1&x_3&x_1&x_2\\x_3&1&y_2&y_1\\x_1&y_2&1&y_3\\x_2&y_1&y_3&1\end{pmatrix}.$$
--   Then $P_a$ is antidegradable iff there exist $x,y$ with $Y(x,y)\succeq0$ and $2a_0a_kx_k+2a_ia_jy_k=\lambda_k$ for all distinct $i,j,k$. For any such pair, the map (94), reconstructed as $\Psi_{x,y}(R)=\tfrac12(\operatorname{Tr}R\,I+\sum_k b_k(R)\sigma_k)$, is CPTP and satisfies $\Psi_{x,y}\circ P_a^C=P_a$, where $b_1=x_1(R_{01}+R_{10})+iy_1(R_{23}-R_{32})$ and the other two are obtained by the cycles $(1,2,3)\mapsto(2,3,1)$ and $(3,1,2)$. Necessarily $|x_k|,|y_k|\le1$.
--
--   This direct PSD criterion remains valid at singular Schur-complement boundaries.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 30, B.3: unital-qubit antidegrader feasibility (94)–(98)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- Appendix B.3, PDF pp.31–33, (94)–(98): necessary and sufficient PSD
feasibility, and the resulting explicit CPTP antidegrader. No inverse at y_k=±1. -/
theorem unitalAntidegraderFeasibility (a : Fin 4 → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hnorm : ∑ k, a k^2 = 1) :
    ((∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap a) ∧ IsAntidegradable witness) ↔ ∃ x y : Fin 3 → ℝ,
      (feasibilityMatrix x y).PosSemidef ∧
      ∀ k : Fin 3, 2*a 0*a k.succ*x k + 2*a (k+1).succ*a (k+2).succ*y k =
        pauliMultipliers a k) ∧
    (∀ x y : Fin 3 → ℝ, (feasibilityMatrix x y).PosSemidef →
      (∀ k : Fin 3, 2*a 0*a k.succ*x k + 2*a (k+1).succ*a (k+2).succ*y k =
        pauliMultipliers a k) →
      IsChannel (pauliAntidegrader x y) ∧
      (∀ rho, pauliAntidegrader x y
        (complementaryChannel (indexedKrausDilation (pauliKraus a)) rho) = qubitPauliMap a rho) ∧
      (∀ k, |x k| ≤ 1 ∧ |y k| ≤ 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
