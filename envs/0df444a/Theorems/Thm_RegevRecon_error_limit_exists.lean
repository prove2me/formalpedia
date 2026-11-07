-- Prove2me | Theorems.Thm_RegevRecon_error_limit_exists
-- name    : RegevRecon.error_limit_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:01.522232+00:00
-- url     : https://prove2.me/theorems/9ea40e7e-445b-40c3-8a4f-a53d3f84627e
-- title:
--   The error limit $\lim_\ell P_{\mathrm{err}}^{(\ell)}$ exists
-- statement:
--   At every $\beta\ge0$, the sequence $P_{\mathrm{err}}^{(\ell)}$ of average root errors converges as $\ell\to\infty$. This makes the threshold (52) meaningful. The page's reason is that increasing the tree depth supplies more channel outputs, and BPQM achieves the minimum root error on each tree.
--
--   Differences from the source: none.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), p.21

import Mathlib
import Definitions.Def_RegevRecon_qLaw

namespace RegevRecon

open Filter Topology

/-- **The error limit exists**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.21: "Note the error limit exists because increasing the tree depth
supplies more channel outputs and BPQM achieves the minimum root error on each tree [PR22]."  -/
theorem error_limit_exists {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ L : ℝ, Tendsto (perr k D S Λ β) atTop (𝓝 L) := by sorry

end RegevRecon
