-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_2_5
-- name    : PermDiameter.Binary.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:19.909223+00:00
-- url     : https://prove2.me/theorems/5ba0faa4-07f4-43b9-bb8a-ef1f215864d9
-- title:
--   Lemma 2.5 — a permutation of order $n_1\cdots n_k$ on $n_1+\dots+n_k$ points, in time polynomial in $d$
-- statement:
--   Given pairwise coprime integers $n_1,\dots,n_k\ge1$, one can compute, in time polynomial in $d=n_1+\dots+n_k$, a permutation $c\in\mathrm{Sym}(\Omega)$ with $|\Omega|=d$ of order $n_1\cdots n_k$:
--   $$|\Omega|=\sum_{i=1}^k n_i,\qquad \operatorname{ord}(c)=\prod_{i=1}^k n_i .$$
--   This realizes cyclic groups of large order as permutation groups of small degree; Lemma 3.2 applies it to $n_i=p_i^4$.
--
--   **Formalization Note.** Since the running time is measured in $d$, the numbers $n_i$ are written in unary (`encUnaryList`); the output is the degree $d$ and the image list of $c$ on `Fin d`. The domain of the map is the subtype of lists of pairwise coprime numbers $\ge1$.
--
--   Differences from the source:
--   - encoding: "time polynomial in d = n₁ + ⋯ + n_k" → TM2ComputableInPolyTime with the n_i in unary and the output (d, c) as degree and image list; reason: the unary input has length between d and 3d + O(log d), so the two bounds agree
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 11, Lemma 2.5

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_PermDiameter_Binary_Problems

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Lemma 2.5.** Given pairwise coprime integers `n₁, …, n_k ≥ 1` (in unary), one can compute
in time polynomial in `d = n₁ + ⋯ + n_k` a permutation `c` of `Fin d` of order `n₁ ⋯ n_k`. -/
theorem lemma_2_5 :
    ∃ F : {ns : List ℕ // (∀ n ∈ ns, 1 ≤ n) ∧ ns.Pairwise Nat.Coprime} → PermWithDegree,
      Nonempty (Turing.TM2ComputableInPolyTime (fun ns => encUnaryList ns.1) encPermWithDegree F) ∧
      ∀ ns, (F ns).1 = ns.1.sum ∧ orderOf (F ns).2 = ns.1.prod := by sorry

end PermDiameter.Binary
