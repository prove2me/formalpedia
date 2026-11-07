-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_10
-- name    : SplayDynOpt.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:27.64597+00:00
-- url     : https://prove2.me/theorems/b710832c-1dcb-4997-b606-61b046f67d2e
-- title:
--   Lemma 10 — internal pairings do not increase the contracted point gap (on ranks)
-- statement:
--   Let $u$ be the owner of a lazy interval $I$ with interval gap $g$, and let $v,w$ be heap-children of $u$ in $I$, with $v$ the winner and $w$ the loser of an internal pairing. Their ranks are integers $r_u,r_v,r_w$, and the point gaps before the pairing are
--   $$
--   x=r_w-r_u-g,\qquad y=r_v-r_u-g\ge0,
--   $$
--   with $r_v<r_w$. After the pairing $w$ joins a growing interval of $v$, whose interval gap is $0$, so its new point gap is $x'=r_w-r_v$. Then:
--
--   1. the contracted point gap of $w$ does not increase: $\operatorname{cpg}(x')\le\operatorname{cpg}(x)$;
--   2. if the pairing is good, that is $\operatorname{cpg}(x)=\operatorname{cpg}(y)$, then it decreases by at least $1$: $\operatorname{cpg}(x')\le\operatorname{cpg}(x)-1$.
--
--   This monotonicity allows the good pairings to be bounded by the total increase in contracted point gaps.
--
--   Differences from the source:
--   - reading: (v, w) an internal pairing of lazy-interval heap-children, with contracted point gaps of heavy paths → integers r_u, r_v, r_w, g with r_v − r_u − g ≥ 0 and r_v < r_w; reason: the lazy intervals are bookkeeping the analysis is free to choose (p.19); the proof's identity x′ = x − y (p.20) carries the whole content. Shared u and g encode internal, r_v < r_w encodes different ranks with w the loser, y ≥ 0 holds since g is the minimum gap of I
--   - generalization: ranks and gaps arising from a heavy-path decomposition → all integers satisfying the two hypotheses; reason: every pairing of the paper gives such integers, so this specializes to the printed statement
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 10, p.20 (Definitions 7–9, p.19)

import Mathlib
import Definitions.Def_SplayDynOpt_cpg

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 10 (on ranks).** Let `v, w` be two heap-children of `u` in the same lazy interval `I`
with interval gap `g`, with point gaps `x = rank w − rank u − g` and `y = rank v − rank u − g ≥ 0`,
and `rank v < rank w`. After the internal pairing, `w` joins the growing interval of `v`
(interval gap `0`), so its new point gap is `x' = rank w − rank v`. Then
`cpg(x') ≤ cpg(x)`, and if the pairing is good (`cpg(x) = cpg(y)`) then `cpg(x') ≤ cpg(x) − 1`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 10, p.20 (with Definitions 7–9, p.19).

**Formalization Note.** The lazy-interval objects of the lemma are unfolded into the integers
`ru, rv, rw` (ranks of the owner `u`, the winner `v` and the loser `w`) and `g` (the interval gap
of `I`). "Internal" is encoded by the common owner and interval gap; "different ranks, `w` the
loser" by `rv < rw`; `y ≥ 0` because `g` is the minimum gap of `I`. Ranks and gaps range over
all integers. -/
theorem lemma_10 :
    ∀ ru rv rw g : ℤ, 0 ≤ rv - ru - g → rv < rw →
      cpg (rw - rv) ≤ cpg (rw - ru - g) ∧
      (cpg (rw - ru - g) = cpg (rv - ru - g) → cpg (rw - rv) ≤ cpg (rw - ru - g) - 1) := by sorry

end SplayDynOpt
