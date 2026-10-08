-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_lemma_4
-- name    : StrategyProofArrow.Dictatorship.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:01.573638+00:00
-- url     : https://prove2.me/theorems/7a0edba6-9230-46bd-bb42-9881e36f112e
-- title:
--   Lemma 4 — the induction step on the number of voters for three alternatives
-- statement:
--   Consider strict committees with three alternatives and $n\ge 1$. Suppose every strategy-proof strict voting procedure $v^{n,3}$ for the $n$ individuals $I_n$ is fully dictatorial or strong alternative-excluding. Then every strict voting procedure $v^{n+1,3}$ for the $n+1$ individuals $I_{n+1}$, with range of $1\le p\le 3$ elements, satisfies
--
--   $$v^{n+1,3}\ \text{strategy-proof}\ \Longrightarrow\ v^{n+1,3}\ \text{fully dictatorial or strong alternative-excluding.}$$
--
--   With Lemma 2 as base case, this yields Lemma 5 for $m=3$ by induction on $n$.
--
--   **Formalization Note** The individuals $I_n$ are `ι` with `Fintype.card ι ≥ 1`, and $I_{n+1}$ is `Option ι`. The induction hypothesis quantifies over all strict voting procedures for `ι` on the same three-element alternative set `A`. $p\le 3$ holds automatically.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 4, p. 22

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 4** (Satterthwaite, p. 22). Three alternatives, `n ≥ 1`. If every strategy-proof
strict voting procedure for the `n` individuals `ι` is fully dictatorial or strong
alternative-excluding, then every strategy-proof strict voting procedure for the `n + 1`
individuals `Option ι` with `1 ≤ p ≤ 3` is fully dictatorial or strong alternative-excluding. -/
theorem lemma_4 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : Fintype.card A = 3)
    (hind : ∀ g : (ι → A → A → Prop) → A, IncentiveCompatible g →
      FullyDictatorial g ∨ StrongAltExcluding g)
    (f : (Option ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by sorry

end StrategyProofArrow.Dictatorship
