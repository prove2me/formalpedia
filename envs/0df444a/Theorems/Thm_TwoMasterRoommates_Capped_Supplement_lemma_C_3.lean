-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_lemma_C_3
-- name    : TwoMasterRoommates.Capped.Supplement.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:34:13.029204+00:00
-- url     : https://prove2.me/theorems/0869f048-cd75-49f9-a5c5-ac38e6dee320
-- title:
--   Lemma C.3 — suffix bound on an outlier's partner quality
-- statement:
--   In a one-master-plus-outliers instance with $s$ outliers, let $o$ be an outlier, $F_o^+$ the followers strictly later than $o$ in the master, and suppose $|F_o^+|\ge s+2$. Let $\theta_o$ be the $(s+2)$-nd smallest value of the multiset $\{r_o(f):f\in F_o^+\}$, counted with multiplicity. Then every weakly stable perfect matching $M$ satisfies
--
--   $$r_o(M(o))\le\theta_o.$$
--
--   This bounds the quality of a remote outlier by a menu $T_o$ of at most $s+2$ values, which the algorithm of Theorem C.1 guesses exactly.
--
--   Differences from the source:
--   - encoding: a weakly stable matching → a weakly stable perfect matching (an involution without fixed points and no blocking pair); reason: §C (p. 18, PDF 19) notes that an even complete instance has no nonperfect weakly stable matching, so the source's matchings are perfect
--   - encoding: complete weak orders (the master ρ and the outlier rows) → integer rank functions, smaller is better, equal values tied; reason: every weak order on a finite set is represented by integer ranks and only comparisons are used (§3)
--   - encoding: θ_o, the (s+2)nd smallest value of the multiset → the k_o-th smallest value with k_o = min(s+2, |F_o^+|), which is the (s+2)nd under the hypothesis |F_o^+| ≥ s+2; reason: one definition serves Lemmas C.3 and C.4, as in §C.1
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 19 (PDF p. 20), Lemma C.3 and the definition of $\theta_o$ before it

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_OneMaster

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Lemma C.3 (suffix bound), Bin Yu, STOC 2027 submission #225, p. 19 (PDF 20): if
`|F_o^+| ≥ s + 2`, every weakly stable perfect matching satisfies `r_o(M o) ≤ θ_o`. -/
theorem lemma_C_3 {N : ℕ} (I : OneMasterInstance N) (o : Fin N) (ho : I.isOut o = true)
    (hlarge : I.s + 2 ≤ (I.Fplus o).card) (M : Fin N → Fin N) (hM : I.IsStable M) :
    I.row o (M o) ≤ I.theta o := by sorry

end TwoMasterRoommates.Capped.Supplement
