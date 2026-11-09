-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_2_10
-- name    : ProportionalTSP.Exact.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:11.119256+00:00
-- url     : https://prove2.me/theorems/cf102aed-4d20-4bb1-8cfe-69f021fb48ca
-- title:
--   Lemma 2.10 — Least normalized prices, rooted tree, distinctness and polynomial computation
-- statement:
--   For every feasible load $d$, let $p=p(d)$, $u=d-e_p$, and $d^{(j)}=u+e_j$ on $L_p$. The prices
--   $$a_j^{(d)}=w(A_d)-w(A_{d^{(j)}})$$
--   are normalized by $a_p^{(d)}=0$ and are coordinatewise least among all normalized prices making $A_d$ tight on $L_p\times R$. Their tight graph equals $F_d=T_{L_p}(u)$ and is a spanning tree on $L_p\sqcup R$. Rooted at $p$, each $r$ has parent $A_d(r)$, each left vertex $l$ has exactly $d_l$ children, and every $l>p$ has a right parent. For fixed $p$, distinct loads have distinct price vectors on $L_p$. A single deterministic program computes prices and the tree in polynomial time. This includes all structural and computational clauses of the lemma.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
--   - encoding: deterministic polynomial or O* running time → a finite RAM program, uniform positive coefficient and natural exponent, and its evaluated instruction count; reason: the explicit language charges combinatorial instructions and allows input reals only to be copied, added, and compared; signed values are pairs of sums
--   - encoding: real prices are computed as differences of assignment values → the program emits two sums per price and their interpreted difference is the price; reason: this realizes the signed-sum implementation on page 12 without introducing a forbidden subtraction instruction
--   - encoding: price vector a^(d) with coordinates only on L_p → a function on all of Fin m, with every clause reading only the coordinates in L_p; reason: the coordinates outside L_p carry no meaning and no clause constrains them
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 2.10, PDF p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_2_10 :
    (∀ (m k : ℕ) [NeZero m], 1 ≤ k → k ≤ m →
      ∀ (w : Fin m → Fin k → ℝ), Generic w → ∀ d : Load m, feasible k d →
      let p := firstPositive d
      let S := tailSet d
      let a := normalizedPrices w d
      let T := normalizedTree w d
      p ∈ S ∧ a p = 0 ∧
      (∀ r, TightEdge w a S (canonical w d r) r) ∧
      (∀ a' : Fin m → ℝ, a' p = 0 →
        (∀ r, TightEdge w a' S (canonical w d r) r) → ∀ j ∈ S, a j ≤ a' j) ∧
      T = restrictedTightGraph w S a ∧ T.IsTree ∧
      (∀ hp : p ∈ S, ∀ r, ∃ l : S, l.val = canonical w d r ∧
        RootParent T (.inl ⟨p,hp⟩) (.inr r) (.inl l)) ∧
      (∀ hp : p ∈ S, ∀ l : S,
        (Finset.univ.filter (fun r : Fin k => RootParent T (.inl ⟨p,hp⟩) (.inr r) (.inl l))).card = d l.val) ∧
      (∀ hp : p ∈ S, ∀ l : S, p < l.val →
        ∃ r : Fin k, RootParent T (.inl ⟨p,hp⟩) (.inl l) (.inr r)) ∧
      (∀ d' : Load m, feasible k d' → firstPositive d' = p →
        (∀ j ∈ S, normalizedPrices w d' j = a j) → d' = d)) ∧
    PolynomialTreeComputation := by sorry

end ProportionalTSP.Exact
