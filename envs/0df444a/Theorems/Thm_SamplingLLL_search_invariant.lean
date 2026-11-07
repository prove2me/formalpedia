-- Prove2me | Theorems.Thm_SamplingLLL_search_invariant
-- name    : SamplingLLL.search_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:59.966302+00:00
-- url     : https://prove2.me/theorems/1bfe5734-0e47-4cef-9d78-d9c67b604b81
-- title:
--   Appendix G, p.66 — search invariant and parent arcs
-- statement:
--   At every stage of the two-rule search, each $H$-component of $Y$ either contains a sampling-good event or is an uncertified singleton. Each accepted event other than the inserted one has a parent among the accepted events with an arc from parent to child in the digraph $H_G$, and iterating the parent reaches the inserted event, so the accepted events have a spanning tree in $H_G$ rooted at the inserted event.
--
--   These links are what let the product in (SLL) pay for the search.
--
--   Differences from the source:
--   - encoding: $\Gamma_s(a)=\Gamma_H(a)\cup\{b:\mathrm{dist}_H(a,b)=2,g_a=0\}$ and $H$-components → $\Gamma_{H_G}(a)$ (the paper's $\Gamma_s(a)=\Gamma_{H_G}(a)$) and `comp`, with a clause equating `comp` to reachability in $H[Y]$; reason: the same objects
--   - encoding: "first earlier accepted $H$-neighbor" and the other canonical choices of parent → existence of a parent map with these properties; reason: the proof uses only these properties
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 2.6, p.66

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

namespace SamplingLLL

/-- Appendix G, p.66: "At every stage, each `H`-component of `Y` either contains a sampling-good event or is
an uncertified singleton", and the parent links are arcs, from parent to child, of the digraph `H_G`, giving
a spanning tree of the accepted events rooted at the inserted event. `comp` is the component in the induced
graph on `Y`, in the full graph `H`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 2.6, p.66. -/
theorem search_invariant {n m : ℕ} (I : AtomicCSP n m) (G S : Finset (Fin m)) (c : Fin m) (t : Leaf m)
    (ht : I.SearchNode G S c t) :
    c ∈ t.1 ∧
    (∀ a (ha : a ∈ t.1) e (he : e ∈ t.1), e ∈ I.comp t.1 a ↔
      (I.H.induce (t.1 : Set (Fin m))).Reachable ⟨a, ha⟩ ⟨e, he⟩) ∧
    (∀ a ∈ t.1, (∃ g ∈ I.comp t.1 a, g ∈ G) ∨ (I.comp t.1 a = {a} ∧ a ∉ G)) ∧
    ∃ par : Fin m → Fin m, ∀ b ∈ t.1.erase c,
      par b ∈ t.1 ∧ b ∈ I.gammaG G (par b) ∧ ∃ k : ℕ, par^[k] b = c := by sorry

end SamplingLLL
