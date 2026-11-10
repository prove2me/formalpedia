-- Prove2me | Theorems.Thm_RobersonCx_lemma_15
-- name    : RobersonCx.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:00.268466+00:00
-- url     : https://prove2.me/theorems/90cb53c3-0709-4117-9bae-d2c3816e5707
-- title:
--   Lemma 15 — deleting a short edge keeps $\mathrm{tw}(D^{(r)}_n)=2r$
-- statement:
--   Let $r\ge2$ and $n>4r^2-2r$. For every short edge $f=\{i,i+1\}$ of $D^{(r)}_n$,
--   $$\mathrm{tw}(D^{(r)}_n-f)=\mathrm{tw}(D^{(r)}_n)=2r.$$
--
--   Together with Lemma 13(iii) (deleting a long edge lowers the width) this is hypothesis (i) of Lemma 19 for the base graph $D^{(r)}_q$.
--
--   Differences from the source:
--   - encoding: $n>4r^2-2r$ → $4r^2<n+2r$ in $\mathbb N$; reason: avoids natural-number subtraction; same instances
--   - encoding: $\mathrm{tw}(\cdot)=2r$ → `TwLE · (2r) ∧ ¬ TwLE · (2r - 1)`; reason: treewidth is Prop-valued; $\mathrm{tw}=2r$ means $\le 2r$ and not $\le 2r-1$; $2r-1\ge1$, no truncation
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 15, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 15 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.4, p.14 (PDF p.16)). Let `r ≥ 2` and `n > 4r² − 2r`. For every short edge `f` of
`D^(r)_n`, `tw(D^(r)_n − f) = tw(D^(r)_n) = 2r`.

**Formalization Note** `n > 4r² − 2r` is `4r² < n + 2r`. A short edge is `{i, i + 1}`. "`tw = 2r`" is
`TwLE · (2r) ∧ ¬ TwLE · (2r − 1)`, stated for both graphs. -/
theorem lemma_15 (r n : ℕ) (hr : 2 ≤ r) (hn : 4 * r ^ 2 < n + 2 * r) (i : ZMod n) :
    TwLE ((circulantD n r).deleteEdges {s(i, i + 1)}) (2 * r) ∧
    ¬ TwLE ((circulantD n r).deleteEdges {s(i, i + 1)}) (2 * r - 1) ∧
    TwLE (circulantD n r) (2 * r) ∧ ¬ TwLE (circulantD n r) (2 * r - 1) := by sorry

end RobersonCx
