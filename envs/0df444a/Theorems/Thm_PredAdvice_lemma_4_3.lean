-- Prove2me | Theorems.Thm_PredAdvice_lemma_4_3
-- name    : PredAdvice.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:52.633547+00:00
-- url     : https://prove2.me/theorems/dedf5391-e439-483f-ac14-a81b3f85f90b
-- title:
--   Lemma 4.3 — trees $T^Q_h \supseteq T^{out}_h$ for the large pairs missed by the sample
-- statement:
--   Let $2\le D\le|V|$. Let $S\subseteq V$ and sets $Q_u$ satisfy $v\in Q_u\iff(u,v)$ is large and $S\cap H_{u,v}=\emptyset$, and put $P_Q=\{(u,v): v\in Q_u\}$. Let $T^{out}_h$ be shortest-path trees directed toward their roots $h$, and let $x(a,v)$ be given for every small pair $(a,v)$ with $x(a,v)\in H_{a,v}$ and $a\in V(T^{out}_{x(a,v)})$. Then there are shortest-path trees $T^Q_h$ directed toward $h$, each containing $T^{out}_h$, with
--   $$
--   \sum_h|E(T^Q_h)|\le\sum_h|E(T^{out}_h)|+|P_Q|, \tag{12}
--   $$
--   and for every $(u,v)\in P_Q$ there are a shortest $u$–$v$ path and its first vertex $a$ with $(a,v)$ small such that $u\in V(T^Q_{x(a,v)})$, i.e. $T^Q_{x(a,v)}$ contains a shortest path from $u$ to $x(a,v)$.
--
--   Each missed large pair costs at most one extra tree edge, which keeps these pairs within the $o(n^2)$ budget.
--
--   Differences from the source:
--   - generalization: T^out_h of Lemma 4.2 and x(·,·) of p.20 → any toward trees rooted at h and any x on small pairs with x(a, v) ∈ H_{a,v} and a ∈ V(T^out_{x(a,v)}); reason: the proof uses only these properties, which the paper's objects have (p.20)
--   - encoding: ∑_h (|E(T^Q_h)| − |E(T^out_h)|) ≤ |P_Q| → ∑_h |E(T^Q_h)| ≤ ∑_h |E(T^out_h)| + |P_Q|; reason: equivalent since T^Q_h contains T^out_h; avoids natural-number subtraction
--   - encoding: T^Q_h contains T^out_h; T^Q_{x(a,v)} contains a shortest u–x(a,v) path → V(T^out_h) ⊆ V(T^Q_h) with equal parents on T^out_h; u ∈ V(T^Q_{x(a,v)}); reason: tree paths of a shortest-path tree are shortest
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 4.3, eq. (12), p.21

import Mathlib
import Definitions.Def_PredAdvice_H
import Definitions.Def_PredAdvice_RootedTree

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 4.3** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §4.2, eq. (12), p.21). Let `S` and `Q_u` be as in Lemma 3.2
(`v ∈ Q_u` iff `(u, v)` is large and `S ∩ H_{u,v} = ∅`), `P_Q := {(u, v) | v ∈ Q_u}`, let
`T^out_h` be shortest-path trees directed toward their roots `h`, and let `x(a, v)` be chosen for
every small pair `(a, v)` with `x(a, v) ∈ H_{a,v}` and `a ∈ V(T^out_{x(a,v)})`. There are
shortest-path trees `T^Q_h` directed toward `h` and containing `T^out_h` with
`∑_h (|E(T^Q_h)| − |E(T^out_h)|) ≤ |P_Q|` (eq. (12)), and for every `(u, v) ∈ P_Q` one can choose a
shortest `u–v` path such that, if `a` is its first vertex with `(a, v)` small, then `T^Q_{x(a,v)}`
contains a shortest path from `u` to `x(a, v)`.

**Formalization Note** The paper's `T^out_h` and `x(·,·)` are those of Lemma 4.2 and p.20 (`x_F` on
separated pairs, `x(a, v) = a` on the other small pairs); the statement assumes only the properties
the proof uses. "Containing `T^out_h`": `V(T^out_h) ⊆ V(T^Q_h)` and the parents agree on the nonroot
vertices of `T^out_h`. Eq. (12) is written without natural-number subtraction, as
`∑ |E(T^Q_h)| ≤ ∑ |E(T^out_h)| + |P_Q|`. "`T^Q_{x(a,v)}` contains a shortest `u–x(a,v)` path" is
`u ∈ V(T^Q_{x(a,v)})`, since tree paths of a shortest-path tree are shortest. -/
theorem lemma_4_3 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D : ℕ)
      (S : Finset V) (Q : V → Finset V) (Tout : V → RootedTree V) (x : V → V → V),
      2 ≤ D → D ≤ Fintype.card V →
      (∀ u v : V, v ∈ Q u ↔ IsLarge G D u v ∧ Disjoint S (H G u v)) →
      (∀ h : V, (Tout h).root = h ∧ IsTowardTree G (Tout h)) →
      (∀ a v : V, IsSmall G D a v → x a v ∈ H G a v ∧ a ∈ (Tout (x a v)).verts) →
      ∃ TQ : V → RootedTree V,
        (∀ h : V, (TQ h).root = h ∧ IsTowardTree G (TQ h) ∧ (Tout h).verts ⊆ (TQ h).verts ∧
          ∀ z ∈ (Tout h).verts, z ≠ h → (TQ h).parent z = (Tout h).parent z) ∧
        ∑ h, (TQ h).edges ≤
          ∑ h, (Tout h).edges + (Finset.univ.filter fun p : V × V => p.2 ∈ Q p.1).card ∧
        ∀ u v : V, v ∈ Q u → ∃ p : List V, IsShortestPath G p u v ∧
          ∃ (pre suf : List V) (a : V), p = pre ++ a :: suf ∧ IsSmall G D a v ∧
            (∀ z ∈ pre, ¬ IsSmall G D z v) ∧ u ∈ (TQ (x a v)).verts := by sorry

end PredAdvice
