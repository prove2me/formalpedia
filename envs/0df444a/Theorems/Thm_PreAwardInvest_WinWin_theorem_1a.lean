-- Prove2me | Theorems.Thm_PreAwardInvest_WinWin_theorem_1a
-- name    : PreAwardInvest.WinWin.theorem_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:54.013343+00:00
-- url     : https://prove2.me/theorems/6b039718-369b-4e06-91bc-1d10288efb45
-- title:
--   Theorem 1(a), p. 16 (PDF 17) — the index policy (3) is an optimal investigation policy for the buyer's problem (1)
-- statement:
--   Assume the standing assumptions and Assumption 2 ($d<\max_i\Delta^t_i$). Let $\tau$ solve $d=\int_\tau^\infty(\epsilon^t-\tau)\,dG(\epsilon^t)$, let $\tau_i=\max\{0,\tau+\Delta^t_i\}$ and $\mu_i(b_i)=b_i-\tau_i$, rank the suppliers by $\mu_i$ from low to high (ties by a fixed priority order $\sigma$), and let $\bar N=\min\{\hat N,\tilde N\}$ with $\tilde N=\min\{n:\tau_{\iota(n+1)}=0\}$. The index policy $\pi^*$ stops in every round $k>\bar N$, and in rounds $k\le\bar N$ it sets
--
--   $$\pi^*_k=\begin{cases}\emptyset, & \text{if } u_k<\min_{i\notin I_k}\mu_i(b_i),\\ \arg\min_{i\notin I_k}\mu_i(b_i), & \text{otherwise},\end{cases}$$
--
--   where $u_k=\min_i\{b_i-\mathbf 1[i\in I_k]t_i\}$ is the lowest updated bid before round $k$. Then $\pi^*$ is admissible and, for every bid vector $b$ with $b_i\in B_i=[0,\bar c_i]$ and every admissible policy $\pi$,
--
--   $$\mathbf E\Big[\min_i\{b_i-\mathbf 1[i\in S^{\pi^*}(b)]t_i\}+|S^{\pi^*}(b)|\,d\Big]\le\mathbf E\Big[\min_i\{b_i-\mathbf 1[i\in S^{\pi}(b)]t_i\}+|S^{\pi}(b)|\,d\Big].$$
--
--   This is the buyer's policy in BIA: the suppliers' bidding game of §4.2 is played against it.
--
--   **Formalization Note.** $\tau$ is any root of the equation; the root is unique when $d>0$, and every root gives an optimal policy when $d=0$. Ties among equal indices are broken by the priority $\sigma$, and the statement holds for every $\sigma$. Policies are deterministic and nonanticipative, read only revealed reductions, and have measurable decision sets; stopping is final (p. 14).
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), p. 16 (PDF 17), Theorem 1(a), eq. (3); problem (1), p. 15 (PDF 16)

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

namespace PreAwardInvest.WinWin

open MeasureTheory

theorem theorem_1a {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (hA2 : Assumption2 P)
    (τ : ℝ) (hτ : IsTauRoot P τ) (σ : Equiv.Perm (Fin N)) :
    (indexPolicy P τ σ).Admissible ∧
      ∀ b : Fin N → ℝ, (∀ i, b i ∈ Set.Icc 0 (cHiI P i)) → ∀ π : Policy N, π.Admissible →
        expCost P (indexPolicy P τ σ) b ≤ expCost P π b := by sorry

end PreAwardInvest.WinWin
