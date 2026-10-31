-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_simple_equiv_standard_gamble
-- name    : ParallelSmallWorlds.SEU.simple_equiv_standard_gamble
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:07.844504+00:00
-- url     : https://prove2.me/theorems/8e38b1a9-83b0-4e2b-8ab9-4dccbe90670c
-- title:
--   Reduction of a simple distribution to a standard gamble, eq. (16)
-- statement:
--   Let a small world satisfy Axioms PSW9–PSW15, let $c^*,c_*$ be a best and a worst consequence with $c^*\succ_S c_*$, and let $\alpha(c)\in[0,1]$ satisfy $c\sim_S c^*\,\alpha(c)\,c_*$ for every consequence $c$. Then for every simple distribution $p=\langle\pi_1,c_1;\dots;\pi_r,c_r\rangle$ over the consequences, the number $\beta=\sum_i\pi_i\alpha(c_i)$ lies in $[0,1]$ and
--
--   $$p\sim_S c^*\Bigl(\sum_{i=1}^r\pi_i\alpha(c_i)\Bigr)c_* .$$
--
--   Comparing two such standard gambles by Axiom PSW11 gives the expected-utility representation of Lemma 2.
--
--   Differences from the source:
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - generalization: the best and worst consequences c∗_w, c_w∗ of PSW12 → any pair cs, cw with cs ≻Sw cw and cs ⪰Sw c ⪰Sw cw for every c; reason: the pair of PSW12 is such a pair
--   - reading: compound gambles ⟨π1,b1;…;πr,br⟩ with prizes bi ∈ C ∪ PSw (p.25), where PSw contains compound gambles → Gamble C = SimpleDist (C ⊕ SimpleDist C): one level of compounding; ⪰Sw on Obj C = C ⊕ Gamble C; reason: PSW14, PSW15 and the proof of Lemma 2 only use gambles whose prizes are consequences or simple distributions (reading R7)
--   - encoding: a simple distribution p ∈ PSw over Cw → SimpleDist C (finitely supported nonnegative weights summing to 1), compared as the object simpObj p (the gamble whose prizes are its consequences); reason: the same objects; the consequence c and the gamble Ψc remain distinct, as in C ∪ PSw
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: PSW14: 'p′ differs from p only in that b′ has been substituted for b'; PSW15: ⟨π1,p1;…;πs,ps⟩ ∼Sw ⟨ρ1,c1;…;ρr,cr⟩ → PSW14 for every gamble g′ with weights substFun g b b′ (the weight of b moved to b′); PSW15 for every simple q with weights reduceFun g, for gambles whose prizes are all simple distributions; reason: the substituted and the reduced gamble are determined by their weights; the axioms quantify over the objects carrying them
--   - encoding: αi with ci ∼Sw c∗_w αi c_w∗, i = 1,…,r → a function α : C → unitInterval with c ∼Sw cs α(c) cw for every c; the conclusion asserts β : unitInterval with β = Σ_c p(c)α(c); reason: the αi of the consequences of p are the values of α on them; the α(c) are a hypothesis, as the page's 'Let ci ∼Sw c∗_w αi c_w∗', so correction C2 (which the page needs to obtain α(c*) and α(c_*)) is not assumed here
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 2, eq. (16), p.45 (PDF p.46)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_UtilityAxioms

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Reduction of a simple distribution to a standard gamble, eq. (16).**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 2, eq. (16), p.45 (PDF p.46): "Let ci ∼Sw c∗_w αi c_w∗, for
i = 1,2,...,r. … use axioms PSW14 and PSW15 to substitute c∗_w αi c_w∗ for ci, in turn, to deduce:
p = ⟨π1,c1;π2,c2;...;πr,cr⟩ ∼Sw c∗_w (Σ_{i=1}^r πiαi) c_w∗."

Under Axioms PSW9–PSW15, let `c*, c_*` be a best and a worst consequence with
`c* ≻Sw c_*`, and let `α(c) ∈ [0,1]` satisfy `c ∼Sw c* α(c) c_*` for every `c`. Then for every
simple distribution `p` over `Cw` the number `β = Σ_c p(c) α(c)` lies in `[0,1]` and
`p ∼Sw c* β c_*`.

**Formalization Note.** The conclusion is an existence statement for `β : unitInterval` with
`β = Σ_c p(c) α(c)`, so it also asserts that this sum lies in `[0,1]`. The equivalents `α(c)` are
a hypothesis, as the page's "Let ci ∼Sw c∗_w αi c_w∗", so correction C2 is not needed here: the
step it repairs is the existence of `α(c*)` and `α(c_*)`, which is `standard_gamble_exists_unique`. -/
theorem simple_equiv_standard_gamble {Θ C : Type*} (W : SmallWorld Θ C)
    (hU : UtilityAxioms W) (cs cw : C)
    (hst : W.strictS (Sum.inl cs) (Sum.inl cw))
    (hbd : ∀ c : C, W.prefS (Sum.inl cs) (Sum.inl c) ∧ W.prefS (Sum.inl c) (Sum.inl cw))
    (α : C → unitInterval)
    (hα : ∀ c : C, W.indiffS (Sum.inl c) (simpObj (SimpleDist.twoPt cs cw (α c)))) :
    ∀ p : SimpleDist C, ∃ β : unitInterval, (β : ℝ) = p.expect (fun c => (α c : ℝ)) ∧
      W.indiffS (simpObj p) (simpObj (SimpleDist.twoPt cs cw β)) := by sorry

end ParallelSmallWorlds.SEU
