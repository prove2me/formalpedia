-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_theorem_7_3
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.theorem_7_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:04:25.743982+00:00
-- url     : https://prove2.me/theorems/47a2648f-7850-4fb1-8367-e2657a5bee08
-- title:
--   Theorem 7.3
-- statement:
--   For integers $n,k\geq0$, embed $S_n$ on the first $n$ letters and $S_k$ on the last $k$ letters of $S_{n+k}$. Write $Z(n)$ for the embedded center of $\mathbb C[S_n]$ and use ambient, unshifted YJM elements. Then
--
--   $$Z(\mathbb C[S_{n+k}],\mathbb C[S_n])=\langle Z(n),S_k,X_{n+1},\ldots,X_{n+k}\rangle.$$
--
--   The source's printed tail group $S_n$ is resolved as $S_k$ by its specified letter set. This retains the full centralizer generation theorem for arbitrary $k$.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 26, Theorem 7.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 7.3 (PDF p.26). Full centralizer equality for every n,k≥0.
The printed tail S_n is read as S_k, as fixed by the specified last k letters. -/
theorem theorem_7_3 (n k : ℕ) :
    Subalgebra.centralizer ℂ (prefixAlgebra (Nat.le_add_right n k) :
      Set (SymmetricAlgebra (n + k))) =
    Algebra.adjoin ℂ ((prefixCenter (Nat.le_add_right n k) :
      Set (SymmetricAlgebra (n + k))) ∪ Set.range (tailElement n k) ∪
      Set.range (fun i : Fin k => yjm (⟨n + i.val, by omega⟩ : Fin (n + k)))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
