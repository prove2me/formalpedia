-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P23_good_set_disjointness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P23.good_set_disjointness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:10:08.330236+00:00
-- url     : https://prove2.me/theorems/28435c5d-4b4e-49b1-bf0a-35a9effa23e2
-- title:
--   Phase-good positions are very bad for Eve, with eventual packing
-- statement:
--   Let $U:\mathbb C^2\to\mathbb C^b\otimes\mathbb C^e$ be an isometry, so $U^\dagger U=I$, defining a memoryless channel to Bob and its fixed complementary channel to Eve. All binary inputs are uniform and entropies are in bits. At recursion depth $n\ge0$, let $N=2^n$ and apply the coherent Arikan encoder $G_N=B_NF^{\otimes n}$, where $F=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$. Amplitude synthesis retains previous bits and averages future bits; phase synthesis retains future bits and averages previous bits, with Bob's coherent copy register $C^N$ retained. Write $r(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1=\sqrt{F(W)}$ for the root fidelity of a binary channel $W$. Fix $0<\beta<1/2$ and put $t_n=2^{-N^\beta}$. Let $G_A,G_P,G_E$ be the respective amplitude-good, phase-good, and Eve-amplitude-good sets, with the strict rule $r(W_N^{(i)})<t_n$. Write $\mathcal A=G_A\cap G_P$ and $\mathcal B=(G_A\cup G_P)^c$. Each set depends on $n$ and $\beta$.
--
--   For every $n$ and every $i\in G_P$,
--   $$
--   r(W_{E,N}^{(i)})>1-2t_n.
--   $$
--   There is a depth $n_0$ such that for every $n\ge n_0$, the sets $G_P$ and $G_E$ are disjoint, as are $\mathcal B$ and $G_P$. If the channel is degradable from Bob to Eve, then $\mathcal B$ and $G_E$ are also disjoint, and
--   $$
--   |G_E|+|G_P|+|\mathcal B|\le N.
--   $$
--   This packing statement is the finite-blocklength input to the vanishing consumption-rate argument.
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, PDF p. 9, Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix

open Filter

open QAlgorithms (Qubits)

open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- Quantitative very-bad conclusion and eventual disjoint-set packing,
Appendix C, PDF p.9. Degradability is needed only for the final two clauses. -/
theorem good_set_disjointness {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (hU : Uᴴ * U = 1) (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1 / 2) :
    (∀ n, ∀ i ∈ goodPhase U n beta,
      1 - 2 * threshold n beta < channelRootFidelity (environmentSplit U n i)) ∧
    (∃ n0 : ℕ, ∀ n ≥ n0,
      Disjoint (goodPhase U n beta) (goodEnvironment U n beta) ∧
      Disjoint (consumedSet U n beta) (goodPhase U n beta) ∧
      (IsDegradable U →
        Disjoint (consumedSet U n beta) (goodEnvironment U n beta) ∧
        (goodEnvironment U n beta).card + (goodPhase U n beta).card +
          (consumedSet U n beta).card ≤ 2 ^ n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P23
