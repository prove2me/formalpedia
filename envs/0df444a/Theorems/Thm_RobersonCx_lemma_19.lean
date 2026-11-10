-- Prove2me | Theorems.Thm_RobersonCx_lemma_19
-- name    : RobersonCx.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:24.633444+00:00
-- url     : https://prove2.me/theorems/fd7660a1-3663-454a-b9da-d9f468e51b4d
-- title:
--   Lemma 19 — minor models follow the Hamilton cycles
-- statement:
--   Let $H,L$ be graphs with specified Hamilton cycles $C_H,C_L$, and let $r\ge1$. Suppose that
--
--   1. $\mathrm{tw}(H)=2r$ and $\mathrm{tw}(H-f)=2r$ for every $f\in E(H)\setminus E(C_H)$;
--   2. every vertex of $L$ belongs to a set $W$ of size $r$ such that $\mathrm{tw}(L-W)\le r$;
--   3. $\mathrm{tw}(L-e)\le 2r-1$ for every $e\in E(C_L)$.
--
--   Then every minor model $(M_h)_{h\in V(H)}$ of $H$ in $L$ partitions $V(L)$ into cyclic intervals on $C_L$, and for $h\ne h'$ the branch sets $M_h,M_{h'}$ are consecutive around $C_L$ if and only if $h,h'$ are adjacent on $C_H$.
--
--   This structural lemma reduces minor exclusion to the counting inequalities of Lemma 20.
--
--   Differences from the source:
--   - encoding: $\mathrm{tw}(\cdot)=2r$ → `TwLE · (2r) ∧ ¬ TwLE · (2r - 1)`; reason: treewidth is Prop-valued; $\mathrm{tw}=2r$ means $\le 2r$ and not $\le 2r-1$; $2r-1\ge1$, no truncation
--   - encoding: specified Hamilton cycle → a bijection `c : ZMod N ≃ V` with consecutive vertices adjacent and $N\ge3$; reason: a cyclic listing of the cycle; same notion
--   - encoding: every minor model partitions $V(L)$ into cyclic intervals → for every family $M$ satisfying the three clauses of Definition 12: the sets cover $V(L)$ and each is a cyclic interval (disjointness is a clause of the model); reason: a partition is a disjoint cover by nonempty sets
--   - encoding: consecutive around $C_L$ → some edge of $C_L$ has one endpoint in each set (`ConsecOnCycle`); reason: for disjoint cyclic intervals covering the cycle this is adjacency of intervals
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 19, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RobersonCx_TwLE
import Definitions.Def_RobersonCx_IsCyclicInterval

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 19 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. B, p.16 (PDF p.18)). Let `H, L` be graphs with specified Hamilton cycles `C_H, C_L`, and
let `r ≥ 1`. Suppose that: (i) `tw(H) = 2r` and `tw(H − f) = 2r` for every `f ∈ E(H) ∖ E(C_H)`; (ii) every vertex
of `L` belongs to a set `W` of size `r` such that `tw(L − W) ≤ r`; (iii) `tw(L − e) ≤ 2r − 1` for every
`e ∈ E(C_L)`. Then every minor model of `H` in `L` partitions `V(L)` into cyclic intervals on `C_L`. Two branch
sets are consecutive around `C_L` if and only if their corresponding vertices are adjacent on `C_H`.

**Formalization Note** Hamilton cycles are cyclic orderings `c : ZMod N ≃ V` (`IsHamCycle`). A minor model is a
family `M : V(H) → Set V(L)` satisfying the three clauses of Definition 12 (the body of `HadwigerConj.IsMinor`);
the conclusion is stated for every such family. "Partitions `V(L)` into cyclic intervals" is: the branch sets
cover `V(L)` (they are disjoint by assumption) and each is a cyclic interval of `C_L`. "Consecutive around `C_L`"
is `ConsecOnCycle` (some edge of `C_L` joins them); "adjacent on `C_H`" is `s(h, h′) ∈ E(C_H)`. -/
theorem lemma_19 {WH VL : Type} [Finite WH] [Finite VL] (H : SimpleGraph WH) (L : SimpleGraph VL)
    {NH NL : ℕ} (cH : ZMod NH ≃ WH) (cL : ZMod NL ≃ VL) (hcH : IsHamCycle H cH) (hcL : IsHamCycle L cL)
    (r : ℕ) (hr : 1 ≤ r)
    (h1 : (TwLE H (2 * r) ∧ ¬ TwLE H (2 * r - 1)) ∧
      ∀ f ∈ H.edgeSet, f ∉ cycleEdges cH →
        TwLE (H.deleteEdges {f}) (2 * r) ∧ ¬ TwLE (H.deleteEdges {f}) (2 * r - 1))
    (h2 : ∀ v : VL, ∃ W : Set VL, v ∈ W ∧ W.ncard = r ∧ TwLE (L.induce Wᶜ) r)
    (h3 : ∀ e ∈ cycleEdges cL, TwLE (L.deleteEdges {e}) (2 * r - 1))
    (M : WH → Set VL) (hM1 : ∀ h, (L.induce (M h)).Connected)
    (hM2 : ∀ h h', h ≠ h' → Disjoint (M h) (M h'))
    (hM3 : ∀ h h', H.Adj h h' → ∃ u ∈ M h, ∃ v ∈ M h', L.Adj u v) :
    (∀ v : VL, ∃ h, v ∈ M h) ∧ (∀ h, IsCyclicInterval cL (M h)) ∧
      ∀ h h', h ≠ h' → (ConsecOnCycle cL (M h) (M h') ↔ s(h, h') ∈ cycleEdges cH) := by sorry

end RobersonCx
