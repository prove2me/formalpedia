-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_Supplement_support_function
-- name    : StabPauli1264.Grouped.Supplement.support_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:53:53.686713+00:00
-- url     : https://prove2.me/theorems/d1b5a3d5-8387-495a-9a1a-5322425411de
-- title:
--   Lemma 9.3 — Support function
-- statement:
--   Let $M$ be a window with frustration graph $G_M$ and $c\in\mathbb R^m$, and write $\alpha_{|c|}(G_M)=\max_{T\text{ independent}}\sum_{i\in T}|c_i|$. Then
--
--   $$h_M(c)\le\alpha_{|c|}(G_M).$$
--
--   Equality holds for all $c\in\mathbb R^m$ if and only if $M$ has no active dependencies. In that case, for any inclusion-maximal independent set $T$ of $G_M$ of maximum $|c|$-weight, the operators $\operatorname{sgn}(c_i)P_i$, $i\in T$, generate a stabilizer group (no product of a subfamily equals $-I$), and every pure stabilizer state that they stabilize attains the maximum $h_M(c)$. Here $\operatorname{sgn}0=1$. The lemma reduces proper ERM to maximum-weight independent set on windows without active dependencies.
--
--   Differences from the source:
--   - encoding: the operators generate a stabilizer group → for every subfamily U ⊆ T the ordered product of the signed operators is not −I; reason: the operators pairwise commute (T is independent in G_M) and square to I, so the generated group consists of these products up to order; it is a stabilizer group exactly when −I is not among them
--   - encoding: a pure stabilizer state stabilized by the group → the projector of a valid tableau fixed by each sgn(c_i)P_i; reason: definition of being stabilized
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Lemma 9.3, p. 23; convention sgn 0 = 1, p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Supplement_Structure
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical

/-- Lemma 9.3 (Support function), p. 23: `h_M(c) ≤ α_{|c|}(G_M)`, with equality for all `c` iff `M`
has no active dependencies; then, for an inclusion-maximal independent `T` of maximum `|c|`-weight,
the operators `sgn(c_i) P_i, i ∈ T`, generate a stabilizer group (no product of them is `−I`), and
every pure stabilizer state they stabilize attains the maximum. -/
theorem support_function {n m : ℕ} (M : Window n m) :
    (∀ c : Fin m → ℝ, supportFn M c ≤ indepWeight (frustrationGraph M) (fun i => |c i|)) ∧
    ((∀ c : Fin m → ℝ, supportFn M c = indepWeight (frustrationGraph M) (fun i => |c i|)) ↔
      NoActiveDep M) ∧
    (NoActiveDep M → ∀ (c : Fin m → ℝ) (T : Finset (Fin m)),
      IsMaximalIndep (frustrationGraph M) T →
      ∑ i ∈ T, |c i| = indepWeight (frustrationGraph M) (fun i => |c i|) →
      (∀ U ⊆ T, (List.ofFn fun i : Fin m =>
          if i ∈ U then ((sgn (c i) : ℂ) • operator M i) else 1).prod ≠ -1) ∧
      ∀ S : Tableau n, IsValidTableau S →
        (∀ i ∈ T, ((sgn (c i) : ℂ) • operator M i) * tableauProjector S = tableauProjector S) →
        ∑ i, c i * response M S i = supportFn M c) := by sorry

end StabPauli1264.Grouped.Supplement
