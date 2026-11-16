-- Prove2me | Theorems.Thm_SignRankMargin_OREquality_Supplement_theorem_14
-- name    : SignRankMargin.OREquality.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:24:24.045197+00:00
-- url     : https://prove2.me/theorems/ed6763fb-6760-43d1-9ffa-b3d6d36e9a9b
-- title:
--   Theorem 14 — sign-rank bounds for OR compositions of regular relations
-- statement:
--   Let $n,D,k$ be integers with $1\le D<n$ and $k\ge1$. Let $B$ be any $n\times n$ Boolean matrix with exactly $D$ ones in every row and exactly $D$ ones in every column; equivalently, $B$ is the biadjacency matrix of a $D$-regular bipartite graph with $n$ vertices on each side. No symmetry, connectedness or diagonal condition is imposed. The OR composition $\mathrm{OR}_k\circ B$ has rows and columns indexed by all tuples $x,y\in[n]^k$, with
--
--   $$
--   (\mathrm{OR}_k\circ B)(x,y)=\mathbf 1[\exists i\in[k]: B(x_i,y_i)=1].
--   $$
--
--   Regard $B$ as a real $0/1$ matrix, let $J$ be the $n\times n$ all-ones matrix, and let $\lambda=\|B-(D/n)J\|_{\mathrm{op}}$ be the Euclidean ($\ell_2\to\ell_2$) operator norm of the centered matrix. Write $\operatorname{rank}_\pm$ for the minimum real rank of a strict sign realization. Then
--
--   $$
--   \operatorname{rank}_\pm(\mathrm{OR}_k\circ B)\le(3D)^k,
--   $$
--
--   and, whenever $n\ge 2^{(6D)^{k+1}}$, also
--
--   $$
--   \left(\frac{D}{\lambda}\right)^k\le\operatorname{rank}_\pm(\mathrm{OR}_k\circ B).
--   $$
--
--   The upper bound needs no size threshold. The lower bound is a direct-sum statement: the sign-rank of the $k$-fold OR composition is at least the $k$-th power of the spectral ratio $D/\lambda$ of a single copy. The equality matrix is the case $D=1$, where it recovers an exponential lower bound of the same shape as the mission's goal.
--
--   **Formalization Note** Sign-rank and OR composition are the published definitions `signRank` and `orComposition` of this mission. Row and column regularity are stated as exact counts of `true` entries. $\lambda$ is the norm of `(Matrix.toEuclideanLin Z).toContinuousLinearMap` for the real matrix $Z(x,y)=\mathbf 1[B(x,y)]-D/n$, the same operator-norm convention as Lemma 13. The lower bound compares real numbers, with the natural-number sign-rank cast to $\mathbb R$; $D/\lambda$ is real division. The source assumptions force $\lambda\ge1$, so no positivity hypothesis on $\lambda$ is added.
--
--   Differences from the source:
--   - encoding: vertex set [n] and coordinates [k]; B ∈ {0,1}^{n×n} with exactly D ones per row and column → Fin n and Fin k indices; B : Matrix (Fin n) (Fin n) Bool with row and column counts of true entries equal to D; reason: finite relabelling; the counts express exactly the source's regularity
--   - encoding: λ = ‖B − (D/n)J‖_op, real comparison (D/λ)^k ≤ rank± → norm of the continuous linear map of the real matrix 1[B]−D/n between Euclidean spaces; signRank cast to ℝ; reason: this is the ℓ₂→ℓ₂ operator norm of the same real matrix, and the comparison is the same real inequality
--   - encoding: if n ≥ 2^{(6D)^{k+1}} then both bounds; the upper bound holds for any n ≥ 1 → unconditional upper bound conjoined with the threshold-conditional lower bound, under the standing 1 ≤ D < n; reason: expresses both source clauses without imposing the threshold on the upper bound
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Theorem 14, p. 15; standing assumptions (B, D, n, λ, OR_k ∘ B) p. 14; proof p. 15

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_SignRankMargin_OREquality_Composition

namespace SignRankMargin.OREquality.Supplement

/-- Theorem 14, p.15 (assumptions p.14). `B` is an arbitrary n×n Boolean matrix with exactly
`D` ones in every row and every column, `1 ≤ D < n`. The upper bound `(3D)^k` holds for all
such `n`; only the lower bound `(D/λ)^k` needs `n ≥ 2^((6D)^(k+1))`. Here
`λ = ‖B − (D/n)J‖_op` is the Euclidean ℓ₂→ℓ₂ operator norm of the centered real matrix,
taken on the continuous linear map between real Euclidean spaces. -/
theorem theorem_14 (n D k : ℕ) (hD : 1 ≤ D) (hDn : D < n) (hk : 1 ≤ k)
    (B : Matrix (Fin n) (Fin n) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) = D)
    (hcols : ∀ y, (∑ x, if B x y then (1 : ℕ) else 0) = D) :
    signRank (orComposition k B) ≤ (3 * D) ^ k ∧
    (2 ^ ((6 * D) ^ (k + 1)) ≤ n →
      ((D : ℝ) / ‖(Matrix.toEuclideanLin
          (fun x y => (if B x y then (1 : ℝ) else 0) - (D : ℝ) / (n : ℝ))
          ).toContinuousLinearMap‖) ^ k ≤
        (signRank (orComposition k B) : ℝ)) := by sorry

end SignRankMargin.OREquality.Supplement
