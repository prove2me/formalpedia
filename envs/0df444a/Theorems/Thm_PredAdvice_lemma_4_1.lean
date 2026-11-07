-- Prove2me | Theorems.Thm_PredAdvice_lemma_4_1
-- name    : PredAdvice.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:55.787515+00:00
-- url     : https://prove2.me/theorems/e4288b46-b263-48f6-930b-936382844398
-- title:
--   Lemma 4.1 — closed subfamilies $\tilde F^{out}_w \subseteq F^{out}_w$, $\tilde F^{in}_w \subseteq F^{in}_w$
-- statement:
--   Let $2\le D\le|V|$, $L\ge1$, $\chi$ be colourings, and let $F^{out}_w,F^{in}_w\subseteq V$ ($w\in V$) have the **coverage property**: $h\in F^{out}_u\cup F^{in}_v$ for every separated small pair $(u,v)$ and every $h\in H^\circ_{u,v}$. Then there are $\tilde F^{out}_w\subseteq F^{out}_w$ and $\tilde F^{in}_w\subseteq F^{in}_w$ with
--
--   1. $h\in\tilde F^{out}_u\cup\tilde F^{in}_v$ for every separated small pair $(u,v)$ and every $h\in H^\circ_{u,v}$;
--   2. $h\in\tilde F^{out}_z$ whenever $h\in\tilde F^{out}_u$ and $z\in H^\circ_{u,h}$;
--   3. $h\in\tilde F^{in}_z$ whenever $h\in\tilde F^{in}_v$ and $z\in H^\circ_{h,v}$.
--
--   Properties 2 and 3 are the closure conditions that let the sets be read as the vertex sets of shortest-path trees (Lemma 4.2).
--
--   Differences from the source:
--   - generalization: the sets F^out_u, F^in_v of §3.3 → any families with the coverage property; reason: the proof uses only the coverage property, which the §3.3 sets have by (7)
--   - generalization: separation with respect to the colourings χ fixed in Lemma 3.3 → separation with respect to any colourings χ : Fin L → V → Fin (2D); reason: the proof uses no property of the specific colourings; the paper's χ is one instance
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 4.1, p.19

import Mathlib
import Definitions.Def_PredAdvice_IsSeparated

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 4.1** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §4.1, p.19). Let `F^out_w, F^in_w ⊆ V` (`w ∈ V`) satisfy the coverage
property: for every separated small pair `(u, v)` and every `h ∈ H°_{u,v}`, `h ∈ F^out_u ∪ F^in_v`.
Then there are families `F̃^out_w ⊆ F^out_w` and `F̃^in_w ⊆ F^in_w` such that

1. for every separated small pair `(u, v)` and every `h ∈ H°_{u,v}`, `h ∈ F̃^out_u ∪ F̃^in_v`,
2. for every `u`, `h ∈ F̃^out_u` and `z ∈ H°_{u,h}`, `h ∈ F̃^out_z`,
3. for every `v`, `h ∈ F̃^in_v` and `z ∈ H°_{h,v}`, `h ∈ F̃^in_z`.

**Formalization Note** The paper applies the lemma to the sets `F^out_u`, `F^in_v` of §3.3, which
have the coverage property by eq. (7); the statement assumes only that property, as the proof
does. `H°_{u,h}` is empty unless `h` is reachable from `u`. -/
theorem lemma_4_1 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ)
      (χ : Colorings V D L) (Fo Fi : V → Finset V), 2 ≤ D → D ≤ Fintype.card V → 1 ≤ L →
      (∀ u v : V, IsSeparated G χ u v → ∀ h ∈ Hcirc G u v, h ∈ Fo u ∪ Fi v) →
      ∃ Fo' Fi' : V → Finset V, (∀ w, Fo' w ⊆ Fo w) ∧ (∀ w, Fi' w ⊆ Fi w) ∧
        (∀ u v : V, IsSeparated G χ u v → ∀ h ∈ Hcirc G u v, h ∈ Fo' u ∪ Fi' v) ∧
        (∀ u h : V, h ∈ Fo' u → ∀ z ∈ Hcirc G u h, h ∈ Fo' z) ∧
        (∀ v h : V, h ∈ Fi' v → ∀ z ∈ Hcirc G h v, h ∈ Fi' z) := by sorry

end PredAdvice
