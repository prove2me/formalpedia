-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_8
-- name    : SwitchingStable.Universal.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:30.415321+00:00
-- url     : https://prove2.me/theorems/e1135606-33b7-4ae5-90a9-761ac93bc8b0
-- title:
--   Lemma 8 — Occurrence count inequalities
-- statement:
--   Fix either direction in the promoted market. Count occurrences $(\mu,u)$ over every stable matching, with the classes of Section 3. Writing $N=nM$ and $M=|\mathrm{Stab}(I)|$, the disjoint class totals give $N=r_0+r_1+e+s+f_a+w+b$, and
--   $$e\le r_0,\qquad w+b\le t_0+r_1,\qquad b\le e_{\rm adj}+f_a+s+d.$$
--   Subset counts such as $d$ are not additional disjoint classes. These inequalities concern all occurrences rather than one realized matching.
--
--   Differences from the source:
--   - encoding: Occurrence counts summed over all stable matchings in I-star → Actual finite occurrence counts cast to real numbers, with N and d expanded from their definitions; reason: Real casts preserve the integer inequalities and avoid truncated count subtraction; the promoted standing assumption is explicit.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 6, PDF p. 7, Lemma 8

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_8 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I) (ε : Direction) :
    let v := occurrenceCounts I ε
    v.N = n * StableCount.numStable I ∧
    v.e ≤ v.r0 ∧ v.w + v.b ≤ v.t0 + v.r1 ∧ v.b ≤ v.eadj + v.fa + v.s + v.d := by sorry

end SwitchingStable.Universal
