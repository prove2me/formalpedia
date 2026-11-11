-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_10
-- name    : RandDelMatroid.Indep.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:30:09.558742+00:00
-- url     : https://prove2.me/theorems/ce91e578-05a6-4ff6-bcc5-d4d6aaed7d0b
-- title:
--   Lemma 10 — triangle inequality for minimum completions
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M$, $u$ a node, and $Q$ a component attached to $u$ through a 3-sum with boundary set $S=\{a,b,c\}$. Let $P_{Q,a},P_{Q,b},P_{Q,c}$ be minimum-cardinality completions of $a$, $b$, $c$ in $Q$. Then
--
--   $$|P_{Q,a}|+|P_{Q,b}|\ \ge\ |P_{Q,c}|.$$
--
--   These inequalities are the hypothesis of the absorption lemma (Lemma 11) for 3-sum components.
--
--   Differences from the source:
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 19, Lemma 10

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_DecompTree

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 10 (p. 19). Let `T` be a clean unordered decomposition tree of a regular matroid `M`, `u`
a node, and `Q` the component attached to `u` through a 3-sum edge `{u, v}` with boundary set
`S = {a, b, c}`. If `P_{Q,a}, P_{Q,b}, P_{Q,c}` are minimum-cardinality completions of `a, b, c`
in `Q`, then `|P_{Q,a}| + |P_{Q,b}| ≥ |P_{Q,c}|`. -/
theorem lemma_10 {β ι : Type} [Fintype ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (u v : ι) (huv : T.Adj u v)
    (a b c : β) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hS : edgeBoundary Mn u v = {a, b, c}) (Pa Pb Pc : Set β)
    (hPa : IsMinCompletion T Mn (attachedComp T u v) (edgeBoundary Mn u v) a Pa)
    (hPb : IsMinCompletion T Mn (attachedComp T u v) (edgeBoundary Mn u v) b Pb)
    (hPc : IsMinCompletion T Mn (attachedComp T u v) (edgeBoundary Mn u v) c Pc) :
    Pc.ncard ≤ Pa.ncard + Pb.ncard := by sorry

end RandDelMatroid.Indep
