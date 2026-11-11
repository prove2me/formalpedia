-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_lemma_3_2
-- name    : PermSymQuery.Quadratic.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:07.574666+00:00
-- url     : https://prove2.me/theorems/c4a2264d-e9e6-4612-99ea-8d9210a900f5
-- title:
--   Lemma 3.2 — exact norm of the restriction error
-- statement:
--   Let $N,s$ be natural numbers, $i\in[N]$, and $H$ a partial injection with $i\notin\operatorname{dom}H$. Put $t=|H|$ and assume $t<s<N$. On the entire compression block $B_{i,H}$, spanned by $|H\rangle$ and its admissible extensions at $i$, the restriction error has exact squared operator norm
--   $$\left\|(\widehat C_iJ_s-J_sC_i^N)\Pi_{B_{i,H}}\right\|^2=\frac{2(N-s)}{(s-t)(N-t-1)}.$$
--   Here $C_i^N$ is full compression, $\widehat C_i$ sampled compression, and $J_s$ the restriction embedding. The projection denotes restriction to that block. Both denominators are positive under the stated assumptions. This equality determines the sampling error without losing its exact size.
--
--   Differences from the source:
--   - encoding: norm restricted to the compression block → ambient operator norm after precomposition with its orthogonal projector; reason: the projector has precisely that block as its range, so the norms agree
--   - encoding: sampled direct sum and maps defined on the stated low database levels → valid pairs span a subspace of the product-basis Euclidean space, with J_s zero off its domain; reason: compression and lookup preserve validity, and every use of J_s is restricted to the source levels
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 3.2, PDF p. 11 (printed p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model
import Definitions.Def_PermSymQuery_Quadratic_Sampled

namespace PermSymQuery.Quadratic

/-- Lemma 3.2, PDF p.11 (printed p.9): exact norm on the whole compression block. -/
theorem lemma_3_2 {N s : ℕ} (i : Fin N) (H : CompPermOracle.PartialPerm N)
    (hi : CompPermOracle.NotInDom H i) (hs : CompPermOracle.size H < s) (hN : s < N) :
    ‖((hatC (s := s) i).comp (restrictJ N s) -
        (restrictJ N s).comp (CompPermOracle.compressU i)).comp (blockProj i H)‖ ^ 2 =
      2 * ((N : ℝ) - s) /
        (((s : ℝ) - CompPermOracle.size H) * ((N : ℝ) - CompPermOracle.size H - 1)) := by sorry

end PermSymQuery.Quadratic
