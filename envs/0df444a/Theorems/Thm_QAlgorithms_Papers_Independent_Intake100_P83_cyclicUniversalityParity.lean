-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_cyclicUniversalityParity
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.cyclicUniversalityParity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:17:26.571456+00:00
-- url     : https://prove2.me/theorems/7979b3d2-1893-411c-b023-a8555f5c895d
-- title:
--   Odd and even cyclic symmetries have different universality behavior
-- statement:
--   For the qubit action $u(a)=\operatorname{diag}(1,e^{2\pi i a/p})$ of $\mathbb Z_p$, let $p\ge2$, $n\ge1$ and $1\le k\le n$. Define $\mathcal V_{n,k}$ by exact finite products of individually invariant gates on at most $k$ arbitrary sites. Then
--
--   $$
--   \begin{aligned}
--   p\text{ odd},\ k\ge p&\quad\Longrightarrow\quad\mathcal V_{n,k}=\mathcal V_{n,n},\\
--   p\text{ even},\ k<n&\quad\Longrightarrow\quad\mathcal V_{n,k}\ne\mathcal V_{n,n}.
--   \end{aligned}
--   $$
--
--   This is full universality, rather than semi-universality or approximation, and it depends on the parity of the cyclic order.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 8, IV D, unnumbered: odd/even cyclic universality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.3,8: odd cyclic symmetries are universal for k >= p; even cyclic
symmetries are not universal for 1 <= k < n. -/
theorem cyclicUniversalityParity (p n k : ℕ) (hp : 2 ≤ p)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (Odd p → p ≤ k → symmetricLocalGroup (cyclicPhases p) n k = symmetricLocalGroup (cyclicPhases p) n n) ∧
    (Even p → k < n → symmetricLocalGroup (cyclicPhases p) n k ≠
      symmetricLocalGroup (cyclicPhases p) n n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
