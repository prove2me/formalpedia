-- Prove2me | Theorems.Thm_RSCapacity_lemma_7_2
-- name    : RSCapacity.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:13.292571+00:00
-- url     : https://prove2.me/theorems/b31ce62f-f7a6-4621-b9be-55730293d2bb
-- title:
--   Lemma 7.2 (Counting points isolated by their support equations)
-- statement:
--   Let $F$ be algebraically closed and let $V_1,\dots,V_t\subseteq\mathbb A^N$ be affine algebraic sets of dimension at most $s$ and total cumulative degree at most $\Delta$. Let $h_1,\dots,h_M$ have degree at most $E\ge1$, with $M\ge1$. Suppose $T\subseteq\bigcup_jV_j$ is finite and every $x\in T$ is assigned a set $S_x\subseteq[M]$ such that $x$ is an isolated point of $\bigcap_{i\in S_x}Z(h_i)$. Then
--   $$|T|\ \le\ \Delta\sum_{a=0}^s(ME)^a .$$
--
--   Applied to the incidence hyperplanes of a list-recovery instance, it counts the candidates that pass the agreement test inside the geometric cover.
--
--   Differences from the source:
--   - encoding: x is an isolated point of ⋂_{i∈S_x} Z(h_i) → some basic open set {g ≠ 0} meets the intersection exactly in x; reason: the Zariski topology has the basic open sets as a basis
--   - encoding: degree of h_i → total degree; reason: the paper's degrees are ordinary total degrees
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 7.2, p.29 (PDF 31)

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry

set_option autoImplicit false

namespace RSCapacity

/-- **Lemma 7.2 (Counting points isolated by their support equations).** Jeronimo,
arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 7.2, p.29 (PDF 31).
Let F be algebraically closed, and let V_1, …, V_t ⊆ 𝔸^N have dimension at most s and total
cumulative degree at most Δ. Let h_1, …, h_M have degree at most E ≥ 1, with M ≥ 1. Suppose
T ⊆ ⋃_j V_j is finite and every x ∈ T is assigned a set S_x ⊆ [M] such that x is an isolated point
of ⋂_{i∈S_x} Z(h_i). Then |T| ≤ Δ ∑_{a=0}^{s} (ME)^a.

**Formalization Note.** The V_j are affine algebraic sets; the degree of h_i is its total degree;
"isolated" is in the Zariski topology (`IsIsolatedIn`); [M] is `Fin M`; the intersection over an
empty S_x is the whole space. -/
theorem lemma_7_2 {F : Type*} [Field F] [IsAlgClosed F] {N : ℕ} (t : ℕ)
    (V : Fin t → Set (Fin N → F)) (hV : ∀ j, IsAlgSet (V j)) (s Δ : ℕ)
    (hdim : ∀ j, algDim (V j) ≤ ((s : ℕ∞) : WithBot ℕ∞)) (hdeg : ∑ j, cdeg (V j) ≤ (Δ : ℕ∞))
    (M E : ℕ) (hM : 1 ≤ M) (hE : 1 ≤ E) (h : Fin M → MvPolynomial (Fin N) F)
    (hh : ∀ i, (h i).totalDegree ≤ E) (T : Set (Fin N → F)) (hTfin : T.Finite)
    (hT : T ⊆ ⋃ j, V j) (Sx : (Fin N → F) → Finset (Fin M))
    (hiso : ∀ x ∈ T, IsIsolatedIn x (⋂ i ∈ Sx x, zeroSet {h i})) :
    T.ncard ≤ Δ * ∑ a ∈ Finset.range (s + 1), (M * E) ^ a := by sorry

end RSCapacity
