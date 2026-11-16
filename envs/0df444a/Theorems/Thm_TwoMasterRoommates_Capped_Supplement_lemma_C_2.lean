-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_lemma_C_2
-- name    : TwoMasterRoommates.Capped.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:33:41.426649+00:00
-- url     : https://prove2.me/theorems/e23aaadc-2987-4c36-afa7-176ac0b4e4c4
-- title:
--   Lemma C.2 — one open follower at a master cut
-- statement:
--   Let $V=F\cup S$ be an instance with one supplied weak master $\rho$ on all agents, followers ranking by $\rho$ and arbitrary outlier rows, and let $M$ be a weakly stable perfect matching. For every threshold $t$, call the agents with $\rho\le t$ processed. If $f,g\in F$ are processed followers whose partners are both unprocessed,
--
--   $$\rho(f)\le t,\quad \rho(g)\le t,\quad \rho(M(f))>t,\quad \rho(M(g))>t,$$
--
--   then $f=g$.
--
--   The tier dynamic program of Theorem C.1 therefore needs to remember at most one pending follower at each cut.
--
--   Differences from the source:
--   - encoding: a weakly stable matching → a weakly stable perfect matching (an involution without fixed points and no blocking pair); reason: §C (p. 18, PDF 19) notes that an even complete instance has no nonperfect weakly stable matching, so the source's matchings are perfect
--   - encoding: a cut immediately after a whole master tier → every integer threshold t, the processed side being {v : ρ(v) ≤ t}; reason: every cut after a whole tier is a threshold cut, and every threshold cut is a cut after a whole tier or the empty cut
--   - encoding: complete weak orders (the master ρ and the outlier rows) → integer rank functions, smaller is better, equal values tied; reason: every weak order on a finite set is represented by integer ranks and only comparisons are used (§3)
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 19 (PDF p. 20), Lemma C.2

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_OneMaster

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Lemma C.2 (one open follower), Bin Yu, STOC 2027 submission #225, p. 19 (PDF 20): at every
cut `ρ ≤ t` of the master, at most one follower on the processed side has a partner on the
unprocessed side in a weakly stable perfect matching. -/
theorem lemma_C_2 {N : ℕ} (I : OneMasterInstance N) (M : Fin N → Fin N) (hM : I.IsStable M)
    (t : ℤ) (f g : Fin N) (hf : I.isOut f = false) (hg : I.isOut g = false)
    (hft : I.ρ f ≤ t) (hgt : I.ρ g ≤ t) (hMf : t < I.ρ (M f)) (hMg : t < I.ρ (M g)) :
    f = g := by sorry

end TwoMasterRoommates.Capped.Supplement
