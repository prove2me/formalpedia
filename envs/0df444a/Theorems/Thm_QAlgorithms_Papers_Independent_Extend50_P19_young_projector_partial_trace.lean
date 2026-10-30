-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_young_projector_partial_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.young_projector_partial_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:04:36.098548+00:00
-- url     : https://prove2.me/theorems/2439fe64-77ad-4eae-9a72-9ae710cce818
-- title:
--   Partial trace of a physical Young isotypic projector
-- statement:
--   Let $d\ge1$ and $N\ge1$ be integers, and let $\mu\vdash_d N$ be a partition of $N$ with at most $d$ rows. Let $P_\mu$ be the full physical isotypic projection in the tensor-permutation Schur-Weyl decomposition of $(\mathbb C^d)^{\otimes N}$, and let $m_{d,\nu}=\dim V_\nu^d$ be the dimension of the corresponding actual Weyl module. If $\operatorname{tr}_1$ traces the first tensor factor, then
--
--   $$\operatorname{tr}_1 P_\mu=m_{d,\mu}\sum_{\substack{\alpha\vdash_d N-1\\\mu=\alpha+\square}}\frac{P_\alpha}{m_{d,\alpha}}.$$
--
--   Here $\mu=\alpha+\square$ means adding one box while retaining a valid partition. Equivalently, the sum removes a box from a row $i$ with $\mu_i>\mu_{i+1}$, using the padded convention $\mu_{d+1}=0$. For $N=1$, the remaining tensor space is one-dimensional. This branching identity is attributed in the source to Audenaert and Christandl et al.
--
--   **Formalization Note** Lean uses $N=n+1$ to express exactly the positive domain of the partial trace.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 4, Lemma 2, (2.6)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Lemma 2, PDF p.4, (2.6), attributed there to Audenaert and
Christandl et al. Written with N=n+1 so tracing the first factor is defined.
Summing over valid predecessors is the removable-box sum, with zero padding. -/
theorem young_projector_partial_trace (d n : ℕ) (hd : 0 < d)
    (mu : Schur.Partition d (n+1)) :
    traceLeft ((Schur.isotypicProjector mu).submatrix
      (fun p : Fin d × (Fin n → Fin d) => Fin.cons p.1 p.2)
      (fun p : Fin d × (Fin n → Fin d) => Fin.cons p.1 p.2)) =
      ∑ alpha : Schur.Partition d n,
        if AddsBox alpha mu then
          ((weylDim mu : ℂ) / (weylDim alpha : ℂ)) • Schur.isotypicProjector alpha
        else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
