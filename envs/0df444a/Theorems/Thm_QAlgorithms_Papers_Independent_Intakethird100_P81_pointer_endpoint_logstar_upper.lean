-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_pointer_endpoint_logstar_upper
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.pointer_endpoint_logstar_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:01:34.614223+00:00
-- url     : https://prove2.me/theorems/c70ac9af-d87b-4b90-93db-80b27592cab5
-- title:
--   Iterated-logarithmic round upper bound
-- statement:
--   Let $g_k$ be the same unrestricted pointer endpoint function on $n$ vertices per side. Write $\log_2^* n$ for the least $j$ with $L_j(n)\le1$, where $L_0(n)=\max\{1,n\}$ and $L_{j+1}(n)=\max\{1,\log_2 L_j(n)\}$. There are absolute $C>0,n_0\ge2$ such that whenever $n\ge n_0$, $k\ge1$ and $k\ge2\log_2^* n$, there is a public-coin, Bob-starting protocol using at most $k$ messages, correct with probability at least $2/3$ on every input, whose worst-case bit cost satisfies
--   $$
--   c\le C\left(\frac{n}{k}+k\right)\log_2 k.
--   $$
--
--   The fixed starting vertex is chosen independently of the inputs, and the final local announcement is uncharged. This keeps both resource terms and makes the iterated-logarithm threshold explicit.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 13, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Corollary 1, PDF p.13: both n/k and k are retained, with fixed error 1/3. -/
theorem pointer_endpoint_logstar_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ (k n : ℕ), 0 < k → n0 ≤ n → 2 * logStar n ≤ k →
      ∀ v1 : Fin n, ∃ (c : ℕ) (P : PublicProtocol (PointerMap n) (PointerMap n) (Vertex n)),
        P.bounded .bob k c ∧ P.computes (endpoint k v1) (1 / 3) ∧
        (c : ℝ) ≤ C * ((n : ℝ) / k + k) * Real.logb 2 k := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
