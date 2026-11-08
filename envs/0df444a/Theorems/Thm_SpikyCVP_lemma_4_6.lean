-- Prove2me | Theorems.Thm_SpikyCVP_lemma_4_6
-- name    : SpikyCVP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:47:21.061209+00:00
-- url     : https://prove2.me/theorems/50dcdf2b-a86d-44d8-9eec-870b9e58085a
-- title:
--   Lemma 4.6 — a non-optimal vector of the right coset is far from optimal
-- statement:
--   Let $1<p<2$, let $\mathcal L\subset\mathbb Z^n$ be a lattice, $t\in\mathbb R^n$, and $v^\ast$ a closest vector of $\mathcal L$ to $t$ in $\ell_p$. Consider any $x\in2\mathcal L+v^\ast$ with $\mathrm{dist}_p(\mathcal L,t)<\|x-t\|_p$, and let $r\in\mathbb R$ satisfy $\|x-t\|_p\le r$ and $\mathrm{dist}_p(\mathcal L,t)\le r$. Then
--
--   $$\|x-t\|_p^p\ \ge\ \mathrm{dist}_p(\mathcal L,t)^p+p(p-1)r^{p-2}.$$
--
--   This gap is what lets the algorithm stop after $O(\log n+\log r_1)$ halvings of $r$: once the excess is below $p(p-1)r^{p-2}$, the vector is a closest vector.
--
--   **Formalization Note** $\mathrm{dist}_p(\mathcal L,t)=\|v^\ast-t\|_p$. A lattice contained in $\mathbb Z^n$ has an integer basis $B\in\mathbb Z^{n\times k}$ with columns independent over $\mathbb R$; the rank $k$ is arbitrary, as in the lemma.
--
--   Differences from the source:
--   - encoding: L ⊂ Zⁿ a lattice → L = L(B) for an integer matrix B ∈ Z^{n×k} with columns linearly independent over ℝ; reason: every basis of a lattice inside Zⁿ has integer entries, so this is every such lattice
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.6, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_SpikyCVP_latt

open PNormReg

namespace SpikyCVP

/-- **Lemma 4.6 (the gap at the end).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 4.6, p.22 (PDF p.24).

Let `p ∈ (1, 2)`, `L ⊂ Zⁿ` a lattice (of any rank `k`, with a basis `B ∈ Z^{n×k}`) and `t ∈ ℝⁿ`, and let `v∗` be a
closest vector.
Consider any `x ∈ 2L + v∗` such that `distp(L, t) < ∥x − t∥p`. Let `r ∈ ℝ` be such that `∥x − t∥p ≤ r` and
`distp(L, t) ≤ r`. Then `∥x − t∥p^p ≥ distp(L, t)^p + p(p − 1)r^{p−2}`.

**Formalization Note.** `distp(L, t) = ∥v∗ − t∥p`. A lattice contained in `Zⁿ` has an integer basis, since its
basis vectors lie in `L`; the columns are linearly independent over `ℝ`. -/
theorem lemma_4_6 {n k : ℕ} (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (B : Matrix (Fin n) (Fin k) ℤ)
    (hB : LinearIndependent ℝ (B.map fun z : ℤ => (z : ℝ)).transpose) (t v : Fin n → ℝ)
    (hv : IsClosestVec p (B.map fun z : ℤ => (z : ℝ)) t v) (x : Fin n → ℝ)
    (hx : x ∈ twoLPlus (B.map fun z : ℤ => (z : ℝ)) v) (hxd : lpNorm p (v - t) < lpNorm p (x - t))
    (r : ℝ) (hxr : lpNorm p (x - t) ≤ r) (hvr : lpNorm p (v - t) ≤ r) :
    lpPow p (v - t) + p * (p - 1) * r ^ (p - 2) ≤ lpPow p (x - t) := by sorry

end SpikyCVP
