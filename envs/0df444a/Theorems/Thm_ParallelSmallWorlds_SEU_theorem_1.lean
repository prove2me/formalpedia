-- Prove2me | Theorems.Thm_ParallelSmallWorlds_SEU_theorem_1
-- name    : ParallelSmallWorlds.SEU.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:27.416391+00:00
-- url     : https://prove2.me/theorems/368bd5d4-fe7d-434f-ac2b-12876d13af70
-- title:
--   Theorem 1: subjective expected utility in every small world with probabilities calibrated on a common reference experiment (corrected: strict PSW5(b); $c\sim_{S_w}\Psi_c$)
-- statement:
--   Consider a family of small worlds $w\in\iota$. Assume that in every world the events form a field $Q_w$, Axioms PSW1–PSW6 hold (with the two empty events identified) together with the strict form C1 of PSW5(b), Axioms PSW9–PSW15 hold together with the correction C2 ($c\sim_{S_w}\Psi_c$), Axiom PSW16 holds, and every act has finitely many consequences and events as fibres. Let $P_w$ be the calibrated probability of world $w$. Then for every $w$:
--
--   1. **(a)** $P_w$ is a finitely additive probability on $Q_w$ ($P_w(\Theta_w)=1$, $P_w\ge0$, additive on disjoint events) agreeing with $\succeq_{\Theta_w}$, and there is $u_w:C_w\to\mathbb R$ such that
--      - $p\succeq_{S_w}q\iff E(u_w\mid p)\ge E(u_w\mid q)$ for all simple distributions $p,q$;
--      - for all acts $a,a'\in A_w$,
--      $$a\succeq_{A_w}a'\iff E(u_w\mid a)\ge E(u_w\mid a'),\qquad E(u_w\mid a)=\sum_{c\in a(\Theta_w)}u_w(c)\,P_w\bigl(a^{-1}\{c\}\bigr);$$
--      - $v$ satisfies the first item in place of $u_w$ if and only if $v=\alpha u_w+\beta$ with $\alpha>0$;
--      - every such $v$ also satisfies the second item in place of $u_w$;
--   2. **(b)** if Axiom PSW7 holds, $P_w$ is countably additive: $\sum_iP_w(R_i)=P_w(\bigcup_iR_i)$ for pairwise disjoint events whose union is an event;
--   3. **(c)** if Axiom PSW8 holds, then for events $R,S,T$ with $T\succ_{\Theta_w}\emptyset$, $P_w(T)>0$ and $(R\mid T)\succeq_{\Theta_w}(S\mid T)\iff P_w(R\cap T)/P_w(T)\ge P_w(S\cap T)/P_w(T)$.
--
--   This is the paper's main result: in parallel small worlds, which may have unrelated beliefs and values, the Bayesian paradigm holds in each, with subjective probabilities on a single scale fixed by the shared reference experiment.
--
--   Differences from the source:
--   - correction: PSW5(b) with weak conclusions only (p.21) → also the strict form (structure CorrectionC1): R ⪰ E, S ⪰ F with one strict gives R ∪ S ≻ E ∪ F, and dually; reason: the proof's step (12) uses 'the implication of PSW5 for strictly more likely'; without it the statement is false: Θ = {a,b}, events ranked by v(∅)=0, v{a}=v{b}=0.6, v(Θ)=1, reference events by Lebesgue measure, satisfies PSW1–PSW8 as printed, yet π{a}+π{b} = 1.2 ≠ 1 = πΘ
--   - correction: PSW10(c) only: c1 ⪰Cw c2 ⟺ Ψc1 ⪰Sw Ψc2 (p.24) → also c ∼Sw Ψc for every consequence c (CorrectionC2); reason: the proof of Lemma 2 uses 'by PSW10(c), c∗_w ∼Sw c∗_w 1 c_w∗', which PSW10(c) does not give; without it the statement is false: Cw = {c*, m, c_*}, every consequence above every gamble, gambles ranked lexicographically by (P(c*), P(m)) of their reduction, satisfies PSW9–PSW15 as printed, and no consequence is indifferent to any gamble, so no α exists
--   - generalization: worlds w = 1,2,…,W → a family of worlds indexed by an arbitrary type ι; reason: taking ι = {1,…,W} gives the paper's statement
--   - encoding: ⪰Θw on the set union Qw ∪ B, in which ∅ is a single element → lik on the disjoint sum Set Θ ⊕ Set ℝ, with ∅_Θ ∼Θw ∅_B imposed (field empty_identified of LikelihoodAxioms); reason: the disjoint sum has two copies of ∅; identifying them restores the paper's single empty set (reading R6), which step (10) uses
--   - generalization: set union Qw ∪ B (an event of Θw equal as a set to a reference event is the same element) → disjoint sum: events of Θ are never identified with reference events; reason: only a weaker hypothesis: a relation on the set union pulls back to one on the disjoint sum satisfying every axiom, so the Lean statement specializes to the paper's
--   - reading: B, 'the σ-field of open and closed intervals on [0,1]'; PSW2 for 'intervals, open or closed' → RefEvents = measurable (Borel) subsets of [0,1]; PSW2 for [a,b] and (a,b), 0 ≤ a ≤ b ≤ 1, including the degenerate {a} and ∅; reason: a σ-field is read as the one these intervals generate (reading R5); half-open intervals are not added to PSW2, which would strengthen it
--   - reading: PΘw, the probability of Lemma 1 → calib W R = inf{π ∈ [0,1] | [0,π] ⪰Θw R}; reason: the proof defines PΘw(R) = πR, the unique π with R ∼Θw [0,π] (p.43); under the axioms the infimum is that π (reading R1)
--   - reading: E(uw | a) = Σ_{θ∈Θw} uw(a(θ))PΘw(θ), and (5) PCw(c′ | a) = Σ_{θ | c′ = a(θ)} PΘw(θ) → actEU W u a = Σ_{c ∈ range a} u(c)·calib W (a⁻¹{c}), and PCw(c | a) = calib W (a⁻¹{c}); each fibre a⁻¹{c} is assumed to be an event; reason: the paper's own rearrangement (18), p.46; it agrees with the printed sum when Θw is finite and singletons are events, and for a finitely additive P on infinite Θw only the fibre form is meaningful (reading R2)
--   - generalization: standing assumption (p.23): Cw finite, or the set of consequences attained by acts finite → each act in Aw has finite range (and PSW16 is assumed for acts of finite range); reason: both of the paper's cases imply that every act has finite range (reading R8)
--   - reading: 'uw(·) is unique up to a positive affine transformation' → a function v represents ⪰Sw on PSw by expected utility iff v = a·u + b for some a > 0 and b (both directions), and every such v also represents ⪰Aw; reason: uniqueness is relative to the representation on PSw (pp.27–28, (7) and the sentence after it): a representation of ⪰Aw alone does not determine u when Aw is small; the clause on ⪰Aw is (7) (reading R3)
--   - reading: (c) 'the use of Bayes Theorem to model the updating of belief in the light of data is justified' → for events R, S, T with T ≻Θw ∅: P(T) > 0 and (R | T) ⪰Θw (S | T) ⟺ P(R∩T)/P(T) ≥ P(S∩T)/P(T); reason: the proof says parts (b) and (c) restate parts (b) and (c) of Lemma 1 (p.46) (reading R4)
--   - reading: compound gambles ⟨π1,b1;…;πr,br⟩ with prizes bi ∈ C ∪ PSw (p.25), where PSw contains compound gambles → Gamble C = SimpleDist (C ⊕ SimpleDist C): one level of compounding; ⪰Sw on Obj C = C ⊕ Gamble C; reason: PSW14, PSW15 and the proof of Lemma 2 only use gambles whose prizes are consequences or simple distributions (reading R7)
--   - encoding: a simple distribution p ∈ PSw over Cw → SimpleDist C (finitely supported nonnegative weights summing to 1), compared as the object simpObj p (the gamble whose prizes are its consequences); reason: the same objects; the consequence c and the gamble Ψc remain distinct, as in C ∪ PSw
--   - encoding: α ∈ [0,1], π ∈ [0,1] and the sets of PSW6/PSW13 'are closed' → α, π : unitInterval; the sets are closed subsets of unitInterval; reason: [0,1] is closed in ℝ, so a subset of it is closed in [0,1] iff it is closed in ℝ
--   - encoding: PSW14: 'p′ differs from p only in that b′ has been substituted for b'; PSW15: ⟨π1,p1;…;πs,ps⟩ ∼Sw ⟨ρ1,c1;…;ρr,cr⟩ → PSW14 for every gamble g′ with weights substFun g b b′ (the weight of b moved to b′); PSW15 for every simple q with weights reduceFun g, for gambles whose prizes are all simple distributions; reason: the substituted and the reduced gamble are determined by their weights; the axioms quantify over the objects carrying them
--   - encoding: PSW16: a ⪰Aw b ⟺ pa ⪰Sw pb, with pa = ⟨PCw(c1 | a),c1; …⟩ → for every pair of simple distributions p, q with p(c) = calib W (a⁻¹{c}) and q(c) = calib W (b⁻¹{c}) for all c: prefA a b ↔ prefS (simpObj p) (simpObj q); reason: pa is the simple distribution with those weights; the axiom does not presuppose that the weights sum to 1 (they do under PSW1–PSW6 and C1, and the verification file exhibits such p)
--   - reading: PSW7 for decreasing events in Qw, conclusion ⋂ Ri ⪰Θw [0,π] → PSW7 required when ⋂ Ri ∈ Qw; reason: ⪰Θw is only defined on Qw ∪ B; when Qw is a σ-field this is the printed axiom
--   - generalization: (b): PΘw countably additive, Qw a σ-field (Lemma 1(b)) → Qw a field; Σ_i P(R_i) = P(⋃_i R_i) for every pairwise disjoint sequence of events whose union is an event; reason: when Qw is a σ-field every union is an event and this is countable additivity
--   - generalization: (a) states that PΘw is finitely additive → (a) also states that PΘw agrees with ⪰Θw on Qw (R ⪰Θw S ⟺ P(R) ≥ P(S)); reason: an additional conclusion, Lemma 1(a), which the proof of Theorem 1 uses; it only strengthens the theorem
--   - encoding: PΘw(R | T) → calib W (R ∩ T) / calib W T, with 0 < calib W T in the conclusion; reason: the definition of conditional probability; positivity, the proof's first sentence, rules out division by zero
--   - encoding: Qw a field → MeasureTheory.IsSetAlgebra W.Q (contains ∅, closed under complement and finite union); reason: the definition of a field of sets
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), Theorem 1, pp.28–29 (PDF pp.29–30); proof p.46 (PDF p.47)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_actEU
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC1
import Definitions.Def_ParallelSmallWorlds_SEU_PSW7
import Definitions.Def_ParallelSmallWorlds_SEU_PSW8
import Definitions.Def_ParallelSmallWorlds_SEU_UtilityAxioms
import Definitions.Def_ParallelSmallWorlds_SEU_CorrectionC2
import Definitions.Def_ParallelSmallWorlds_SEU_PSW16

namespace ParallelSmallWorlds.SEU

open SmallWorld

/-- **Theorem 1: subjective expected utility in every small world, with probabilities calibrated
on the common reference experiment.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), Theorem 1, pp.28–29 (PDF pp.29–30), proved p.46 (PDF p.47):
"∀w = 1,2,...,W (a) Axioms PSW1—PSW6, PSW9—PSW16 are sufficient to justify the seu representation
with finitely additive probabilities of the mdm's preferences over Aw, viz.: a ⪰Aw a′ ⟺
E(uw | a) ≥ E(uw | a′). where: E(uw | a) = Σ_{θ∈Θw} uw(a(θ))PΘw(θ), uw(·) is unique up to a
positive affine transformation, and PΘw(·) is finitely additive. (b) If Axiom PSW7 holds, PΘw(·)
is countably additive. (c) If Axiom PSW8 holds, the use of Bayes Theorem to model the updating of
belief in the light of data is justified."

For a family of small worlds `W w`, `w ∈ ι`, each with a field of events `Qw`, satisfying Axioms
PSW1–PSW6 (with `∅_Θ ∼ ∅_B`) and the correction C1, Axioms PSW9–PSW15 and the correction C2, and
Axiom PSW16, and whose acts have finitely many consequences with fibres in `Qw`: for every `w`,
with `P = calib (W w)`,

* **(a)** `P` is a finitely additive probability on `Qw` agreeing with `⪰Θw`, and there is
  `u : Cw → ℝ` such that (i) `p ⪰Sw q ⟺ E(u | p) ≥ E(u | q)` on simple distributions; (ii)
  `a ⪰Aw a′ ⟺ E(u | a) ≥ E(u | a′)` on acts, `E(u | a) = Σ_c u(c) P(a⁻¹{c})`; (iii) `v` satisfies
  (i) iff `v = α·u + β` with `α > 0`; (iv) every such `v` also represents `⪰Aw` as in (ii);
* **(b)** if PSW7 holds, `P` is countably additive on `Qw`;
* **(c)** if PSW8 holds, then for events `R, S, T` with `T ≻Θw ∅`, `P(T) > 0` and
  `(R | T) ⪰Θw (S | T) ⟺ P(R ∩ T)/P(T) ≥ P(S ∩ T)/P(T)`.

**Formalization Note.** `PΘw` is the calibrated probability `calib` the paper constructs. The
sum over states is the rearrangement (18) over consequences (`actEU`). Clause (c) is Lemma 1(c),
which the proof says it restates. Countable additivity in (b) is for every disjoint sequence of
events whose union is an event, so that `Qw` may be a field. The corrections C1 and C2 are the
separate hypotheses `hC1` and `hC2`. -/
theorem theorem_1 {ι : Type*} {Θ C : ι → Type*} (W : ∀ w, SmallWorld (Θ w) (C w))
    (hQ : ∀ w, MeasureTheory.IsSetAlgebra (W w).Q)
    (hL : ∀ w, LikelihoodAxioms (W w)) (hC1 : ∀ w, CorrectionC1 (W w))
    (hU : ∀ w, UtilityAxioms (W w)) (hC2 : ∀ w, CorrectionC2 (W w))
    (h16 : ∀ w, PSW16 (W w))
    (hA : ∀ w, ∀ a ∈ (W w).A, (Set.range a).Finite ∧ ∀ c, a ⁻¹' {c} ∈ (W w).Q) :
    ∀ w,
      -- (a) finitely additive probability agreeing with the likelihood relation
      ((calib (W w) Set.univ = 1 ∧ (∀ R ∈ (W w).Q, 0 ≤ calib (W w) R) ∧
        (∀ R ∈ (W w).Q, ∀ S ∈ (W w).Q, Disjoint R S →
          calib (W w) (R ∪ S) = calib (W w) R + calib (W w) S) ∧
        (∀ R ∈ (W w).Q, ∀ S ∈ (W w).Q,
          (W w).lik (Sum.inl R) (Sum.inl S) ↔ calib (W w) S ≤ calib (W w) R)) ∧
      -- (a) the subjective expected utility representation, u unique up to positive affine maps
      ∃ u : C w → ℝ,
        (∀ p q : SimpleDist (C w),
          (W w).prefS (simpObj p) (simpObj q) ↔ q.expect u ≤ p.expect u) ∧
        (∀ a ∈ (W w).A, ∀ a' ∈ (W w).A,
          (W w).prefA a a' ↔ actEU (W w) u a' ≤ actEU (W w) u a) ∧
        (∀ v : C w → ℝ,
          (∀ p q : SimpleDist (C w),
            (W w).prefS (simpObj p) (simpObj q) ↔ q.expect v ≤ p.expect v) ↔
          ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, ∀ c, v c = α * u c + β) ∧
        (∀ v : C w → ℝ, (∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, ∀ c, v c = α * u c + β) →
          ∀ a ∈ (W w).A, ∀ a' ∈ (W w).A,
            ((W w).prefA a a' ↔ actEU (W w) v a' ≤ actEU (W w) v a))) ∧
      -- (b) countable additivity under PSW7
      (PSW7 (W w) → ∀ R : ℕ → Set (Θ w), (∀ i, R i ∈ (W w).Q) →
        Pairwise (Function.onFun Disjoint R) → (⋃ i, R i) ∈ (W w).Q →
        HasSum (fun i => calib (W w) (R i)) (calib (W w) (⋃ i, R i))) ∧
      -- (c) conditional likelihood represented by conditional probability under PSW8
      (PSW8 (W w) → ∀ R ∈ (W w).Q, ∀ S ∈ (W w).Q, ∀ T ∈ (W w).Q,
        (W w).strictLik (Sum.inl T) (Sum.inl ∅) →
        0 < calib (W w) T ∧
        ((W w).condLik R S T ↔
          calib (W w) (S ∩ T) / calib (W w) T ≤ calib (W w) (R ∩ T) / calib (W w) T)) := by sorry

end ParallelSmallWorlds.SEU
