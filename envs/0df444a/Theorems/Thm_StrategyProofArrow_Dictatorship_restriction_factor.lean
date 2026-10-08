-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_restriction_factor
-- name    : StrategyProofArrow.Dictatorship.restriction_factor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:14.201644+00:00
-- url     : https://prove2.me/theorems/4c844c46-9f33-4271-b3a6-cd4ed8138ab1
-- title:
--   Proof of Theorem 1, (27)–(28) — a strategy-proof procedure induces a strategy-proof procedure on its range
-- statement:
--   Let $v^{nm}$ be a strategy-proof, strong alternative-excluding strict voting procedure for $n\ge 1$ individuals with range $T=T_p$, where $m>p\ge 3$. Then there is a strict voting procedure $v^{np}$ for the $p$ alternatives of $T$ such that, for every strict ballot set $B\in\rho^n_m$,
--
--   $$v^{np}\bigl[\theta_T(B_1),\dots,\theta_T(B_n)\bigr]=v^{nm}(B_1,\dots,B_n),$$
--
--   and $v^{np}$ is strategy-proof. Here $\theta_T(B_i)$ is the strong order on $T$ obtained from $B_i$ by deleting the alternatives outside $T$.
--
--   This is displays (27)–(28) of the proof of Theorem 1 and the sentence following them: it reduces a procedure with a proper range to one whose range is its whole alternative set, to which the full-range case of Lemma 5 applies.
--
--   **Formalization Note** The alternative set of $v^{np}$ is the subtype `↥(range f)`, and $\theta_T(B_i)$ is the restriction of $B_i$'s strict relation to that subtype (a strict total order again). $v^{np}$ is a function on all relation profiles over the subtype; the identity is required at restrictions of strict ballot sets, and strategy-proofness quantifies over strict ballot sets on the subtype. The hypotheses include the proof's case assumptions: strong alternative exclusion and $m>p\ge 3$. The context hypothesis $n\ge 1$ (Theorem 1) is kept. The paper derives the claim from Lemma 6, stated for $n\ge 2$; the claim itself is stated here for $n\ge 1$, as in Theorem 1, whose proof uses it.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §3, proof of Theorem 1, displays (27)–(28) and the following sentence, p. 27

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Proof of Theorem 1, (27)–(28)** (Satterthwaite, p. 27). In the proof's case of a
strategy-proof, strong alternative-excluding strict voting procedure `f` with a proper range
`T = T_p` of at least three alternatives, `f` factors through the restriction of ballots to `T`:
there is a
strict voting procedure `g` for the alternative set `T` (a subtype) with
`g(θ_T(B_1), …, θ_T(B_n)) = f(B)` for every strict ballot set `B`, and `g` is strategy-proof. -/
theorem restriction_factor {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f)
    (hstrong : StrongAltExcluding f)
    (hp : 3 ≤ (range f).ncard)
    (hproper : (range f).ncard < Fintype.card A) :
    ∃ g : (ι → range f → range f → Prop) → range f,
      (∀ P : ι → A → A → Prop, IsPrefProfile P →
        ((g (fun i (x y : range f) => P i x y) : A) = f P)) ∧
      IncentiveCompatible g := by sorry

end StrategyProofArrow.Dictatorship
