-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_stable_graph_identification
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.stable_graph_identification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:38:06.677621+00:00
-- url     : https://prove2.me/theorems/7c2a280b-9b63-47cc-975c-6e13619fa25a
-- title:
--   Unnumbered (3.23): stable-label graph identification
-- statement:
--   Let $n\ge1$ and let $K=M/2$ be a nonnegative half-integer with $n\ge2K$. At level $\ell=m/2\le K$, tensor-space labels are partitions $\lambda$ of $n$ at integer levels and of $n-1$ at half levels, with $|\lambda|-\lambda_1\le\lfloor\ell\rfloor$. Stable labels are partitions $\mu$ with $|\mu|\le\lfloor\ell\rfloor$. Deleting the first row gives bijections
--
--   $$\lambda\longmapsto\lambda_{>1}$$
--
--   at every level through $K$, and these bijections preserve and reflect every edge between consecutive half levels. Stable edges are stay/remove followed by stay/add; tensor-space edges remove and add one box. This identifies the stable truncations of the two graphs. The cutoff corrects the printed claim of an isomorphism through level $n$.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 23, Unnumbered (3.23): stable-label graph identification

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Stable truncation of the branching graph, PDF p.23, (3.23).
SOURCE CORRECTION: levels through doubled cutoff `M ≤ n`, rather than through level `n`.
The row equations pin each bijection to deletion of the first row. -/
theorem stable_graph_identification (n M : ℕ) (_hn : 0 < n) (_hM : M ≤ n) :
    ∃ e : (m : Fin (M + 1)) → TensorLabel n m.val ≃ StableLabel m.val,
      (∀ m : Fin (M + 1), ∀ lam : TensorLabel n m.val, ∀ i : ℕ,
        ((e m lam).val).rowLen i = lam.val.rowLen (i + 1)) ∧
      (∀ (m : ℕ) (hm : m < M) (lam : TensorLabel n m) (mu : TensorLabel n (m + 1)),
        tensorEdge m lam.val mu.val ↔
          stableEdge m ((e ⟨m, by omega⟩ lam).val) ((e ⟨m + 1, by omega⟩ mu).val)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
