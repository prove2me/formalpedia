-- Prove2me | Theorems.Thm_SameStatePairs_top_k_spectral_theorem
-- name    : SameStatePairs.top_k_spectral_theorem
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T21:04:38.325417+00:00
-- url     : https://prove2.me/theorems/b62bb58d-7ecf-427d-852e-aec4be2d4fc0
-- title:
--   Theorem 1 (rank at least $k$): minimizers span a top-$k$ eigenspace of the same-state operator
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$ and $\sum_zp(z)=1$, let $X$ be a finite observation space with channel $P_{X\mid Z}$ and $P_X(x)>0$, and let $k\ge1$. Let $\lambda_1\ge\lambda_2\ge\cdots$ be the eigenvalues of $T_s$ on the centred subspace of $L^2(P_X)$, and consider the global minimisers of $L_\varepsilon$ in eq. (3) over encoders $f:X\to\mathbb{R}^k$ that are centred and whitened under $P_X$.
--
--   1. If $\operatorname{rank}(T_s)\ge k$, then for every $0<\varepsilon\le1$ the span of any global minimiser is a $k$-dimensional subspace of the top eigenspace of $T_s$ (the span of the centred eigenfunctions with eigenvalue $\ge\lambda_k$), and it contains every centred eigenfunction with eigenvalue $>\lambda_k$.
--   2. If $0<\varepsilon\le1$ and $\lambda_k>\lambda_{k+1}$, the span of every global minimiser is the top-$k$ eigenspace, and any two global minimisers $f,f'$ satisfy $f'=Qf$ for some $Q\in O(k)$.
--
--   **Formalization Note** $\operatorname{rank}(T_s)$, eigenvalues and eigenspaces are taken on the centred subspace. In item 2 the gap hypothesis is required only when $\lambda_{k+1}$ exists, i.e. $k+1\le|X|-1$ (convention $\lambda_{|X|}=-\infty$). Item 2 is stated for $\varepsilon>0$ (as in the proof) and without the hypothesis $\operatorname{rank}(T_s)\ge k$, which the proof does not use. "Right multiplication by $O(k)$" of the matrix of $f$ is written $f'(x)=Qf(x)$.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 4.1, Theorem 1, eq. (3), p. 6; proof in Appendix A.1, p. 11

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem top_k_spectral_theorem {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq X] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (κ : Z → X → ℝ) (hκ : IsChannel κ) (hX : ∀ x, 0 < obsLaw p κ x) (hk : 1 ≤ k) :
    (k ≤ obsRank p κ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : X → Fin k → ℝ, IsGlobalMin (obsLaw p κ) (mixPairLaw p κ ε) f →
        Module.finrank ℝ (coordSpan f) = k ∧ coordSpan f ≤ topSpace p κ k ∧
          strictTopSpace p κ k ≤ coordSpan f) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (k + 1 < Fintype.card X → obsEig p κ (k + 1) < obsEig p κ k) →
      (∀ f : X → Fin k → ℝ, IsGlobalMin (obsLaw p κ) (mixPairLaw p κ ε) f →
        coordSpan f = topSpace p κ k) ∧
      (∀ f f' : X → Fin k → ℝ, IsGlobalMin (obsLaw p κ) (mixPairLaw p κ ε) f →
        IsGlobalMin (obsLaw p κ) (mixPairLaw p κ ε) f' →
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ x, f' x = rot Q (f x))) := by sorry

end SameStatePairs
