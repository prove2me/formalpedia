-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_3
-- name    : SamplingLLL.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:53.688857+00:00
-- url     : https://prove2.me/theorems/696fd320-c156-4428-80d3-66c2b5f957d0
-- title:
--   Lemma A.3, p.20 — last-defect router
-- statement:
--   Fix $B\ne\{c\}$ with $c\in B\subseteq C$, and call a leaf $t$ active when $Y_t\subseteq B$ and $L_t\cap B=\emptyset$. On an active leaf, choose the element $d$ of $B\setminus\{c\}$ queried last, and let the new leaf be the one reached on input $Y_t\triangle\{d\}$. This map sends active leaves to active leaves, is an involution, and reverses the parity of $|Y_t|-1$.
--
--   This is the local cancellation rule behind (1), used as an algorithm by the circuit.
--
--   Differences from the source:
--   - encoding: a finite constraint set and a decision tree → constraints indexed by a `Fin m`, the tree as a next-query rule on pairs (Y, N); reason: every finite set relabels to `Fin m`, and a node of a tree is determined by (Y, N); no instance changes
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.3, p.20

import Mathlib
import Definitions.Def_SamplingLLL_Exploration

set_option autoImplicit false

namespace SamplingLLL

/-- Lemma A.3 (Last-defect router), p.20: for `B ≠ {c}`, `routerLeaf` is an involution on the active
leaves and reverses the parity of `|Y_t| - 1`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.3, p.20. -/
theorem lemma_A_3 {m : ℕ} (C : Finset (Fin m)) (c : Fin m) (hc : c ∈ C) (next : NextQuery m)
    (hnext : IsExploration C c next) (B : Finset (Fin m)) (hcB : c ∈ B) (hBC : B ⊆ C)
    (hne : B ≠ {c}) (t : Leaf m) (ht : t ∈ leaves C c next) (hact : Active C t B) :
    routerLeaf next c B t ∈ leaves C c next ∧
    Active C (routerLeaf next c B t) B ∧
    routerLeaf next c B (routerLeaf next c B t) = t ∧
    sign (routerLeaf next c B t) = - sign t := by sorry

end SamplingLLL
