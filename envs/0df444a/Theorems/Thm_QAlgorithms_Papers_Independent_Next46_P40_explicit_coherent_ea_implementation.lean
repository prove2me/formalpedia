-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_explicit_coherent_ea_implementation
-- name    : QAlgorithms.Papers.Independent.Next46.P40.explicit_coherent_ea_implementation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:54:36.615027+00:00
-- url     : https://prove2.me/theorems/efecd040-37bd-46e9-97e7-bdc9376b4ca6
-- title:
--   Explicit environment-preserving coherent EA implementation
-- statement:
--   Fix a finite-dimensional CPTP channel $\mathcal N:A'\to B$, an isometric dilation $U:A'\to BE$, and a normalized pure resource $\phi^{A'R}$. Let $\theta=(\mathcal N\otimes\mathrm{id}_R)\phi$. For every final tolerance $\epsilon>0$ and rate slack $\delta>0$, there are positive internal tolerances $\tau,\eta$ and a threshold such that every sufficiently large positive blocklength $n$ admits a message count $M\ge1$ and one coherent code, chosen before all messages and message superpositions. Its rate obeys $\log_2 M\ge n(I(R;B)_\theta-\delta)$. Put
--
--   $$\epsilon'_n=4(\tau+\sqrt{8\tau})+16\,2^{-n\eta}\le\epsilon.$$
--
--   The code consists of input unitaries $V_k$, receiver transfer unitaries $T_k$ satisfying $(V_k\otimes I)\phi^{\otimes n}=(I\otimes T_k)\phi^{\otimes n}$, and one complete receiver POVM $\{\Lambda_k\}$. Each encoder exactly preserves $\rho^{\otimes n}$ and has decoding probability at least $1-\epsilon'_n$. The coherent decoder is computed as the positive-square-root measurement isometry followed by controlled $T_k^\dagger$. For every $k$, its full pure output has real overlap at least $1-\epsilon'_n$ with the unencoded dilation output tensored with $|k\rangle_J$, and the corresponding density operators differ in full trace norm by at most $\sqrt{8\epsilon'_n}$.
--
--   The same bound holds uniformly for every normalized message superposition, including one entangled with an arbitrary finite external reference chosen after the code, when that reference, the sender label $K$, receiver label $J$, resource halves, and inaccessible $E^n$ are all retained. This is the finite coherent-decoupling interface; it makes no diamond-norm claim after discarding $K$.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 5, (38)–(39), ensuing coherifiability claim

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

/-- PDF p.5, (38)--(39) and the ensuing coherifiability claim on pp.5--6.
The code and all internal tolerances precede every message and coherent
superposition and external reference size. The global estimate retains F,
BOTH K and J and all of E;
no diamond estimate for a discarded-label channel is asserted. Rule O and
subsequent resource cancellation remain attributed to [23]. -/
theorem explicit_coherent_ea_implementation
    [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (N : Superop A B) (hN : IsChannel N)
    (U : Matrix (B × E) A ℂ) (hU : Uᴴ * U = 1)
    (hdilation : ∀ X, traceRight (conjSuperop U X) = N X)
    (v : EuclideanSpace ℂ (A × R)) (hv : ‖v‖ = 1) :
    ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
      ∃ tau eta : ℝ, 0 < tau ∧ 0 < eta ∧
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
        packingError tau eta n ≤ eps ∧
        ∃ m : ℕ, 0 < m ∧ ∃ code : CoherentEACode A B R n m,
          (n : ℝ) * (mutualInformation (leftTensor N (pureDensity v)) - delta) ≤
            Real.logb 2 (m : ℝ) ∧ coherentEACorrect U v code (packingError tau eta n) ∧
          ∀ s : ℕ, 0 < s →
          ∀ amplitude : EuclideanSpace ℂ (Fin s × Fin m), ‖amplitude‖ = 1 →
            traceNorm (pureDensity (coherentlyControlledOutput (n := n) (m := m) (s := s) U v code amplitude) -
              pureDensity (coherentlyControlledTarget (n := n) (m := m) (s := s) U v amplitude)) ≤
                Real.sqrt (8 * packingError tau eta n) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
