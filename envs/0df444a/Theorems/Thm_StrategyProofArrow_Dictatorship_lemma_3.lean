-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_lemma_3
-- name    : StrategyProofArrow.Dictatorship.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:57.566242+00:00
-- url     : https://prove2.me/theorems/606c614c-7132-4fc7-b804-98d21f402d68
-- title:
--   Lemma 3 — voters 1, …, n cannot manipulate an (n+1)-voter procedure iff all its sections are strategy-proof
-- statement:
--   Consider a strict committee $\langle I_{n+1},S_3,v^{n+1,3},T_p\rangle$ with $n\ge 1$ and $1\le p\le 3$. Write a ballot set as $(B,B_{n+1})$ with $B=(B_1,\dots,B_n)$. For each strict ballot $b$ of individual $n+1$, the **section** $v^{n,3}_b(B)=v^{n+1,3}(B,b)$ is a strict voting procedure for the first $n$ individuals; for three alternatives there are six of them, display (6). Then
--
--   $$\Bigl(\text{no } i\in I_n \text{ can manipulate } v^{n+1,3} \text{ at any } (B,B_{n+1})\in\rho^{n+1}_3\Bigr)\iff \Bigl(\text{every section } v^{n,3}_b \text{ is strategy-proof}\Bigr).$$
--
--   Individual $n+1$ is excluded from the left-hand side; including them would make the right-to-left direction false, since a family of strategy-proof sections can still be manipulated by individual $n+1$. The lemma is the device by which the induction on $n$ passes from $n$ to $n+1$ individuals.
--
--   **Formalization Note** The $n+1$ individuals are `Option ι`, with `none` the individual $n+1$ and `some i` the individual $i\in I_n$; the section for ballot $b$ is `sectionAt f b`. The six sections of display (6) are the sections for the six strict orders on three alternatives, quantified as "every strict total order $b$". The paper prints the ballot set as $(B,B_{n+1})\in\pi^{n+1}_m$; since the committee is strict this is read as $\rho^{n+1}_3$, and it prints $v^n_1,\dots,v^n_6$ for $v^{n,3}_1,\dots,v^{n,3}_6$. The hypotheses $n\ge 1$ and $p\ge 1$ are kept as printed although the equivalence does not need them.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 3 and display (6), pp. 16–17

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 3** (Satterthwaite, pp. 16–17). Let the committee have `n + 1` individuals, encoded as
`Option ι` with `none` the individual `n + 1`, three alternatives, `n ≥ 1` and `1 ≤ p ≤ 3`. No
individual `i ∈ I_n` (individual `n + 1` excluded) can manipulate `f` at any strict ballot set if
and only if every section `sectionAt f b` (voter `n + 1` casting the strict ballot `b`) is a
strategy-proof strict voting procedure for the `n` remaining individuals. -/
theorem lemma_3 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : Fintype.card A = 3)
    (f : (Option ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard) :
    (∀ P : Option ι → A → A → Prop, IsPrefProfile P →
        ∀ (i : ι) (r' : A → A → Prop), IsStrictTotalOrder A r' →
          ¬ P (some i) (f (Function.update P (some i) r')) (f P)) ↔
      ∀ b : A → A → Prop, IsStrictTotalOrder A b → IncentiveCompatible (sectionAt f b) := by sorry

end StrategyProofArrow.Dictatorship
