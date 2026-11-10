-- Prove2me | Theorems.Thm_RobersonCx_corollary_18
-- name    : RobersonCx.corollary_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:03.366003+00:00
-- url     : https://prove2.me/theorems/fc3483b8-8eb6-4697-b16d-bbc93154f89f
-- title:
--   Corollary 18 — deleting a short edge keeps $\mathrm{tw}(B^{(r)}_n)=2r$
-- statement:
--   Let $r\ge2$ and $n>4r^2-2r$. For every short edge $f=v_iu_{i+1}$ of $B^{(r)}_n$,
--   $$\mathrm{tw}(B^{(r)}_n-f)=\mathrm{tw}(B^{(r)}_n)=2r.$$
--
--   This is hypothesis (i) of Lemma 19 for the base graph $B^{(r)}_q$ with its Hamilton cycle of spokes and long edges.
--
--   Differences from the source:
--   - encoding: $n>4r^2-2r$ → $4r^2<n+2r$ in $\mathbb N$; reason: avoids natural-number subtraction; same instances
--   - encoding: $\mathrm{tw}(\cdot)=2r$ → `TwLE · (2r) ∧ ¬ TwLE · (2r - 1)`; reason: treewidth is Prop-valued; $\mathrm{tw}=2r$ means $\le 2r$ and not $\le 2r-1$; $2r-1\ge1$, no truncation
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Corollary 18, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx

/-- Corollary 18 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.5, p.16 (PDF p.18)). Let `r ≥ 2` and `n > 4r² − 2r`. For every short edge `f` of
`B^(r)_n`, `tw(B^(r)_n − f) = tw(B^(r)_n) = 2r`.

**Formalization Note** `n > 4r² − 2r` is `4r² < n + 2r`. A short edge is `v_iu_{i+1}` =
`s(Sum.inr i, Sum.inl (i + 1))`. "`tw = 2r`" is `TwLE · (2r) ∧ ¬ TwLE · (2r − 1)`, for both graphs. -/
theorem corollary_18 (r n : ℕ) (hr : 2 ≤ r) (hn : 4 * r ^ 2 < n + 2 * r) (i : ZMod n) :
    TwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + 1))}) (2 * r) ∧
    ¬ TwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + 1))}) (2 * r - 1) ∧
    TwLE (splitB n r) (2 * r) ∧ ¬ TwLE (splitB n r) (2 * r - 1) := by sorry

end RobersonCx
