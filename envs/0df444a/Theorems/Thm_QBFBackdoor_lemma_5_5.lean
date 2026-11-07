-- Prove2me | Theorems.Thm_QBFBackdoor_lemma_5_5
-- name    : QBFBackdoor.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:09.446238+00:00
-- url     : https://prove2.me/theorems/3a756029-44fe-4b2e-b2ce-865ca4d769ee
-- title:
--   Lemma 5.5 — splitting a $\Gamma_{\mathrm{AFF}}$ formula into $r$ parts
-- statement:
--   Let $\phi$ be a $\Gamma_{\mathrm{AFF}}$ formula on variables $X$ and let $r\ge2$. Then there are a set $Y$ of fresh variables and $\Gamma_{\mathrm{AFF}}$ formulas $\phi_1,\dots,\phi_r$ on $X\cup Y$ such that:
--
--   1. $|\phi_j|\le|\phi|$ for every $j\in[r]$ (atom counts);
--   2. for every proper subset $T\subsetneq[r]$ and every assignment $\alpha$ to $X$, some assignment to $Y$ satisfies $\bigwedge_{j\in T}\phi_j$ together with $\alpha$;
--   3. every part $\phi_j$ is satisfiable together with every assignment to $X$;
--   4. for every assignment $\alpha$ to $X$,
--   $$
--   \alpha\models\phi \iff \alpha \text{ extends to an assignment satisfying } \textstyle\bigwedge_{j=1}^r\phi_j ;
--   $$
--   5. for every quantifier prefix $Q$ on $X$,
--   $$
--   Q.\phi \iff Q\,\exists Y.\ \textstyle\bigwedge_{j=1}^r\phi_j .
--   $$
--
--   The parts can each be satisfied, and so can any proper subcollection of them, without constraining $X$, while all of them together enforce $\phi$. This is what lets squishing keep the existential player's freedom (Lemma 5.7).
--
--   Differences from the source:
--   - generalization: |ϕj| = O(|ϕ|) → |ϕj| ≤ |ϕ|; reason: the explicit count; the proof gives exactly |ϕ| atoms per part, and the explicit bound implies the O-bound
--   - encoding: variables X ∪ Y with Y fresh → Fin (n + N), with Y the last N variables and assignments Fin.append α y; reason: relabelling; Y is disjoint from X
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Lemma 5.5, pp.23–24

import Mathlib
import Definitions.Def_QBFBackdoor_DQBF

namespace QBFBackdoor

/-- **Lemma 5.5 (splitting a `Γ_AFF` formula into `r` parts).** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), pp.23–24: "Let ϕ be a
formula in ΓAFF on variables X. For every integer r ≥ 2, one can construct formulas ϕ1, . . . , ϕr
in ΓAFF on variables X ∪ Y, where Y is fresh, such that 1. for every j ∈ [r], |ϕj| = O(|ϕ|);
2. for every proper subset T ⊂ [r] and every assignment α to X, there is an assignment to Y
satisfying ⋀_{j∈T} ϕj under α; 3. for every assignment α to X, α |= ϕ if and only if α extends to
an assignment satisfying ⋀_{j=1}^r ϕj. In particular, every part is satisfiable for every
assignment to X, and, for every quantifier prefix Q on X, Q.ϕ ⇐⇒ Q∃Y. ⋀_{j=1}^r ϕj."

**Formalization Note** `X` is `Fin n` and `X ∪ Y` is `Fin (n + N)`, with the fresh variables
`Y` the last `N` (an assignment is `Fin.append α y`). `|ϕ|` counts atoms (§3.1). Item 1's
`O(|ϕ|)` is stated as the explicit `|ϕ_j| ≤ |ϕ|` (the proof gives exactly `|ϕ|` atoms per part).
Item 2 includes `T = ∅`. The clause "every part is satisfiable for every assignment to X" is stated separately. In the prefix clause `Q∃Y` is the prefix `q` followed by `N`
existential variables. -/
theorem lemma_5_5 {n : ℕ} (ϕ : List (GAtom n)) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (N : ℕ) (parts : Fin r → List (GAtom (n + N))),
      (∀ j, (parts j).length ≤ ϕ.length) ∧
      (∀ T : Finset (Fin r), T ≠ Finset.univ → ∀ α : Fin n → Bool,
        ∃ y : Fin N → Bool, ∀ j ∈ T, SatAll (parts j) (Fin.append α y)) ∧
      (∀ j, ∀ α : Fin n → Bool, ∃ y : Fin N → Bool, SatAll (parts j) (Fin.append α y)) ∧
      (∀ α : Fin n → Bool,
        SatAll ϕ α ↔ ∃ y : Fin N → Bool, ∀ j, SatAll (parts j) (Fin.append α y)) ∧
      (∀ q : Fin n → Bool,
        PrefixHolds q (SatAll ϕ) ↔
          PrefixHolds (Fin.append q (fun _ => true)) (fun x => ∀ j, SatAll (parts j) x)) := by sorry

end QBFBackdoor
