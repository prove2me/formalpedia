-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_lemma_2
-- name    : ParallelSmallWorlds.SEU.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:08.885068+00:00
-- url     : https://prove2.me/theorems/e792f5c3-cd97-452c-8eb1-c161afb7e702
-- title:
--   Lemma 2: an expected-utility representation of $\succeq_{S_w}$, unique up to positive affine maps (corrected: $c\sim_{S_w}\Psi_c$)
-- statement:
--   Let a small world satisfy Axioms PSW9–PSW15 and the correction C2. Then there is a utility function $u:C\to\mathbb R$ such that
--
--   1. $c\succeq_C c'\iff u(c)\ge u(c')$ for all consequences $c,c'$;
--   2. for all simple distributions $p,q$ over the consequences,
--   $$p\succeq_S q\iff E(u\mid p)\ge E(u\mid q);$$
--   3. a function $v:C\to\mathbb R$ satisfies 2 in place of $u$ if and only if $v=a\,u+b$ for some $a>0$ and some $b\in\mathbb R$.
--
--   This is the von Neumann–Morgenstern part of the paper, in each small world; unlike the probabilities, the utilities of different worlds are not on a common scale.
--
--   Differences from the source:
--   - correction: PSW10(c) only: c1 ⪰Cw c2 ⟺ Ψc1 ⪰Sw Ψc2 (p.24) → also c ∼Sw Ψc for every consequence c (CorrectionC2); reason: the proof of Lemma 2 uses 'by PSW10(c), c∗_w ∼Sw c∗_w 1 c_w∗', which PSW10(c) does not give; without it the statement is false: Cw = {c*, m, c_*}, every consequence above every gamble, gambles ranked lexicographically by (P(c*), P(m)) of their reduction, satisfies PSW9–PSW15 as printed, and no utility represents the lexicographic order
--   - encoding: ∀ w = 1,2,…,W (each small world separately) → one arbitrary small world W : SmallWorld Θ C; reason: every hypothesis and every conclusion concerns a single world; the statement for an arbitrary world is the statement for each w
--   - generalization: 'In the presence of Axioms PSW1—PSW8' → PSW1–PSW8 not assumed; reason: the proof of Lemma 2 does not use them; the Lean statement specializes to the paper's
--   - generalization: Cw finite, or the consequences attained by acts finite (standing assumption, p.23) → Cw an arbitrary type; reason: the proof never uses finiteness: every simple distribution has finite support
--   - reading: 'uw(·) is unique up to a positive affine transformation' → a function v represents ⪰Sw on PSw by expected utility iff v = a·u + b for some a > 0 and b (both directions); reason: uniqueness is relative to the representation on PSw (pp.27–28, (7) and the sentence after it) (reading R3)
--   - reading: compound gambles ⟨π1,b1;…;πr,br⟩ with prizes bi ∈ C ∪ PSw (p.25), where PSw contains compound gambles → Gamble C = SimpleDist (C ⊕ SimpleDist C): one level of compounding; ⪰Sw on Obj C = C ⊕ Gamble C; reason: PSW14, PSW15 and the proof of Lemma 2 only use gambles whose prizes are consequences or simple distributions (reading R7)
--   - encoding: a simple distribution p ∈ PSw over Cw → SimpleDist C (finitely supported nonnegative weights summing to 1), compared as the object simpObj p (the gamble whose prizes are its consequences); reason: the same objects; the consequence c and the gamble Ψc remain distinct, as in C ∪ PSw
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: PSW14: 'p′ differs from p only in that b′ has been substituted for b'; PSW15: ⟨π1,p1;…;πs,ps⟩ ∼Sw ⟨ρ1,c1;…;ρr,cr⟩ → PSW14 for every gamble g′ with weights substFun g b b′ (the weight of b moved to b′); PSW15 for every simple q with weights reduceFun g, for gambles whose prizes are all simple distributions; reason: the substituted and the reduced gamble are determined by their weights; the axioms quantify over the objects carrying them
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Lemma 2, pp.26–27 (PDF pp.27–28); proof p.45 (PDF p.46)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_UtilityAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC2

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Lemma 2: an expected-utility representation of `⪰Sw`, unique up to positive affine
transformations.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Lemma 2, pp.26–27 (PDF pp.27–28), proved p.45 (PDF p.46): "Axioms
PSW9—PSW15 imply that ∀w = 1,2,...,W, ∃uw : C → ℜ, an agreeing utility function on Cw such that
∀c,c′ ∈ Cw: c ⪰Cw c′ ⟺ uw(c) ≥ uw(c′). Moreover, ∀p,q ∈ PSw: p ⪰Sw q ⟺ E(uw(c) | p) ≥
E(uw(c) | q) … In addition, uw(·) is unique up to a positive affine transformation."

Under Axioms PSW9–PSW15 and correction C2 there is `u : Cw → ℝ` such that

1. `c ⪰Cw c′ ⟺ u(c) ≥ u(c′)` for all consequences;
2. `p ⪰Sw q ⟺ E(u | p) ≥ E(u | q)` for all simple distributions `p, q` over `Cw`;
3. a function `v : Cw → ℝ` satisfies 2 (in place of `u`) if and only if `v = a·u + b` for some
   `a > 0` and some `b`.

**Formalization Note.** Correction C2 (`c ∼Sw Ψc`) is needed (see `CorrectionC2` for the
counterexample without it). Uniqueness is relative to clause 2 and is stated in both directions.
Axioms PSW1–PSW8, in whose "presence" the page states the lemma, are not assumed, and `Cw` is
arbitrary (the paper's standing finiteness assumption is not used). -/
theorem lemma_2 {Θ C : Type*} (W : SmallWorld Θ C) (hU : UtilityAxioms W) (hC2 : CorrectionC2 W) :
    ∃ u : C → ℝ, (∀ c c' : C, W.prefC c c' ↔ u c' ≤ u c) ∧
      (∀ p q : SimpleDist C, W.prefS (simpObj p) (simpObj q) ↔ q.expect u ≤ p.expect u) ∧
      (∀ v : C → ℝ,
        (∀ p q : SimpleDist C, W.prefS (simpObj p) (simpObj q) ↔ q.expect v ≤ p.expect v) ↔
          ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ c : C, v c = a * u c + b) := by sorry

end ParallelSmallWorlds.SEU
