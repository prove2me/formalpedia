-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_standard_gamble_exists_unique
-- name    : ParallelSmallWorlds.SEU.standard_gamble_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:30.442183+00:00
-- url     : https://prove2.me/theorems/1fcae75f-25be-4a5e-8c3b-a5f41706b31c
-- title:
--   Standard-gamble equivalent: $c\sim_{S_w}c^*_w\,\alpha\,c_{w*}$ for a unique $\alpha$ (corrected: $c\sim_{S_w}\Psi_c$)
-- statement:
--   Let a small world satisfy Axioms PSW9–PSW13 and the correction C2 ($c\sim_S\Psi_c$ for every consequence $c$), and let $c^*,c_*$ be a best and a worst consequence with $c^*\succ_S c_*$ and $c^*\succeq_S c\succeq_S c_*$ for every $c$. Then for every consequence $c$ there is exactly one $\alpha\in[0,1]$ with
--
--   $$c\sim_S c^*\,\alpha\,c_* .$$
--
--   The number $\alpha$ is the standard-gamble utility of $c$ on the scale $u(c^*)=1$, $u(c_*)=0$; Lemma 2 is built from it.
--
--   Differences from the source:
--   - correction: PSW10(c) only: c1 ⪰Cw c2 ⟺ Ψc1 ⪰Sw Ψc2 (p.24) → also c ∼Sw Ψc for every consequence c (CorrectionC2); reason: the proof of Lemma 2 uses 'by PSW10(c), c∗_w ∼Sw c∗_w 1 c_w∗', which PSW10(c) does not give; without it the statement is false: Cw = {c*, m, c_*}, every consequence above every gamble, gambles ranked lexicographically by (P(c*), P(m)) of their reduction, satisfies PSW9–PSW15 as printed, and no consequence is indifferent to any gamble, so no α exists
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - generalization: the best and worst consequences c∗_w, c_w∗ of PSW12 → any pair cs, cw with cs ≻Sw cw and cs ⪰Sw c ⪰Sw cw for every c; reason: the pair of PSW12 is such a pair
--   - reading: compound gambles ⟨π1,b1;…;πr,br⟩ with prizes bi ∈ C ∪ PSw (p.25), where PSw contains compound gambles → Gamble C = SimpleDist (C ⊕ SimpleDist C): one level of compounding; ⪰Sw on Obj C = C ⊕ Gamble C; reason: PSW14, PSW15 and the proof of Lemma 2 only use gambles whose prizes are consequences or simple distributions (reading R7)
--   - encoding: a simple distribution p ∈ PSw over Cw → SimpleDist C (finitely supported nonnegative weights summing to 1), compared as the object simpObj p (the gamble whose prizes are its consequences); reason: the same objects; the consequence c and the gamble Ψc remain distinct, as in C ∪ PSw
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 2, p.45 (PDF p.46)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_UtilityAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC2

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **The standard-gamble equivalent of a consequence.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 2, p.45 (PDF p.46): "For each w = 1,2,...,W, we argue from
PSW9 – PSW13, analogously to the proof of part (a) of Lemma 3, that ∀c ∈ Cw, there exists a
unique α such that c ∼Sw c∗_w α c_w∗."

Under Axioms PSW9–PSW13 and correction C2 (`c ∼Sw Ψc`), let `c*` and `c_*` be a best and a worst
consequence with `c* ≻Sw c_*` (as provided by PSW12). Then for every consequence `c` there is
exactly one `α ∈ [0,1]` with `c ∼Sw c* α c_*`.

**Formalization Note.** Correction C2 is needed at `c = c*` and `c = c_*` (the page invokes
"PSW10(c)" for `c* ∼Sw c* 1 c_*`, which PSW10(c) as printed does not give). The statement is
for every best/worst pair, not only the one PSW12 provides; "Lemma 3" on the page means
Lemma 1. -/
theorem standard_gamble_exists_unique {Θ C : Type*} (W : SmallWorld Θ C)
    (hU : StandardGambleAxioms W) (hC2 : CorrectionC2 W) (cs cw : C)
    (hst : W.strictS (Sum.inl cs) (Sum.inl cw))
    (hbd : ∀ c : C, W.prefS (Sum.inl cs) (Sum.inl c) ∧ W.prefS (Sum.inl c) (Sum.inl cw)) :
    ∀ c : C, ∃! α : unitInterval, W.indiffS (Sum.inl c) (simpObj (SimpleDist.twoPt cs cw α)) := by sorry

end ParallelSmallWorlds.SEU
