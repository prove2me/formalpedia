-- Prove2me | Theorems.Thm_RSCapacity_lemma_6_4
-- name    : RSCapacity.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:02.249037+00:00
-- url     : https://prove2.me/theorems/9f0953cd-9692-4c82-b664-add9d9500160
-- title:
--   Lemma 6.4 (Graph of a bounded-degree rational map)
-- statement:
--   Let $K$ be algebraically closed and $U\subseteq\mathbb A^m$ constructible with $\dim U\le s$ and $\operatorname{cdeg}(U)\le\Delta$. Suppose a rational map $\phi:U\to\mathbb A^N$ has coordinates $\phi_j=N_j/H^{e_j}$, where $H$ is nonzero on $U$, $e_j,L$ are nonnegative integers with $e_j\le L$, and
--   $$\deg H,\ \deg N_j,\ L\deg H\ \le\ E .$$
--   Then the Zariski closure of the graph of $\phi$ has dimension at most $s$ and cumulative degree at most
--   $$\Delta(2E+2)^s .$$
--
--   This bounds the geometric cover produced by the lifted jets of Lemma 6.7.
--
--   Differences from the source:
--   - reading: dim U and cdeg(U) of a constructible set U → dimension and cumulative degree of its Zariski closure; reason: the only reading under which Lemma 6.3's use of U is consistent
--   - encoding: degree of an irreducible affine variety (its projective closure) → Heintz's degree: max |V ∩ E| over affine subspaces E of codimension dim V with V ∩ E finite; reason: Heintz 1983, Definition 1 and Remark 2; the two degrees agree
--   - reading: In particular, when s is fixed and E, N are polynomially bounded in a parameter D, the graph has degree D^{O_s(1)} → not a separate clause; reason: it is the main bound read with Δ also bounded, which the sentence leaves implicit
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 6.4, p.24 (PDF 26); §6.2, p.24

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry

set_option autoImplicit false

namespace RSCapacity

open MvPolynomial

/-- **Lemma 6.4 (Graph of a bounded-degree rational map).** Jeronimo, arXiv:2609.05870 (held
version of November 1, 2026, sha256 9a0069bd…), Lemma 6.4, p.24 (PDF 26), over an algebraically
closed field (§6.2, p.24). Let U ⊆ 𝔸^m be constructible, with dim U ≤ s and cdeg(U) ≤ Δ. Suppose a
rational map ϕ : U → 𝔸^N has all coordinates of the form ϕ_j = N_j/H^{e_j}, where H is nonzero on
U, e_j, L are nonnegative integers with e_j ≤ L, and deg H, deg N_j, L deg H ≤ E. Then the Zariski
closure of the graph of ϕ has dimension at most s and cumulative degree at most Δ(2E + 2)^s.

**Formalization Note.**
* dim U and cdeg U of the constructible set U are those of its Zariski closure (`algDim`, `cdeg`
  are computed from I(U)); degrees of N_j and H are total degrees.
* The graph {(u, ϕ(u)) : u ∈ U} lies in 𝔸^{m+N} (`ratGraph`, coordinates of u first).
* The page's closing sentence ("In particular, when s is fixed and E, N are polynomially bounded
  in a parameter D, the graph has degree D^{O_s(1)}") is a reading of the bound when Δ is also
  bounded; it is not a separate clause. -/
theorem lemma_6_4 {K : Type*} [Field K] [IsAlgClosed K] {m N : ℕ} (U : Set (Fin m → K))
    (hU : IsConstructible U) (s Δ : ℕ) (hdim : algDim U ≤ ((s : ℕ∞) : WithBot ℕ∞))
    (hdeg : cdeg U ≤ (Δ : ℕ∞)) (H : MvPolynomial (Fin m) K)
    (Nf : Fin N → MvPolynomial (Fin m) K) (e : Fin N → ℕ) (L E : ℕ)
    (hH : ∀ u ∈ U, eval u H ≠ 0) (he : ∀ j, e j ≤ L) (hHE : H.totalDegree ≤ E)
    (hNE : ∀ j, (Nf j).totalDegree ≤ E) (hLE : L * H.totalDegree ≤ E) :
    algDim (zClosure (ratGraph U H Nf e)) ≤ ((s : ℕ∞) : WithBot ℕ∞) ∧
      cdeg (zClosure (ratGraph U H Nf e)) ≤ ((Δ * (2 * E + 2) ^ s : ℕ) : ℕ∞) := by sorry

end RSCapacity
