-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_young_projector_partial_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.young_projector_partial_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:59:02.388109+00:00
-- url     : https://prove2.me/theorems/0b4261e2-75b2-43d6-9e4b-bcf9d0f628f1
-- title:
--   Corollary 10: partial trace of a Young isotypic projector
-- statement:
--   Let $d\ge1$, $k\ge1$, $n=r+2k$ with $r>0$, and $\mu\vdash_d r+k$. Write $P_\mu$ for the full physical Young isotypic projector on $r+k=n-k$ registers. For each $\beta\vdash_d r$, let $m_{\mu/\beta}$ count saturated reduced Young paths from $\beta$ to $\mu$, and let $m_\mu,m_\beta$ be their physical Schur–Weyl multiplicities. Then
--
--   $$
--   \operatorname{Tr}_{r+1,\ldots,r+k}P_\mu
--   =\sum_{\beta\vdash_d r}m_{\mu/\beta}\frac{m_\mu}{m_\beta}P_\beta.
--   $$
--
--   The trace is unnormalized, and absent paths contribute zero. This formula retains all restriction copies and provides the projector version of the iterated trace rule.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 13, Corollary 10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Corollary 10: trace of the full Young isotypic projector, with the saturated
path count. Here n=r+2k and r>0 preserves the source's strict 2k<n preamble
(PDF p.13, (81)-(82)). -/
theorem young_projector_partial_trace (d r k : ℕ) (hd : 0 < d)
    (hr : 0 < r) (hk : 0 < k) (mu : QAlgorithms.Schur.Partition d (r+k)) :
    traceFinalQudits (k := k) (QAlgorithms.Schur.isotypicProjector mu) =
      ∑ beta : QAlgorithms.Schur.Partition d r,
        ((pathCount beta mu : ℂ) * (mpbtSchurMultiplicity mu : ℂ) / (mpbtSchurMultiplicity beta : ℂ)) •
          QAlgorithms.Schur.isotypicProjector beta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
