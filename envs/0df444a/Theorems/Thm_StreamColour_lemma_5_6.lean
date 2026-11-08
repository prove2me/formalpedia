-- Prove2me | Theorems.Thm_StreamColour_lemma_5_6
-- name    : StreamColour.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:48.577315+00:00
-- url     : https://prove2.me/theorems/4fe5215f-a9bd-4b13-a40f-9ae26135ba69
-- title:
--   Lemma 5.6 — blocks in a minimum-singleton partition are nearly joined to the singleton core
-- statement:
--   Let $X$ be an expanded piece, under the hypotheses of Lemma 5.4, let $q=\Delta-k$, and let $\mathcal P$ be a partition of $X$ into at most $q$ nonempty independent sets with the fewest singleton classes. Let $K$ be its singleton core and $D$ a block.
--
--   1. If $|D|\ge3$, every vertex of $D$ is adjacent to every vertex of $K$. Consequently
--   $$\sum_{v\in D}e_X(v)\le|D|(\Delta-|K|)=O(h^2).$$
--   2. If $D=\{x,y\}$, at least one of $x,y$ is adjacent to all but at most one vertex of $K$. Consequently
--   $$e_X(x)+e_X(y)\le\tfrac7{25}\Delta+\Delta-|K|+1=\tfrac7{25}\Delta+O(h).$$
--
--   These bounds control the neighbours of a block outside its piece, which is what lets the piece's classes be coloured last.
--
--   Differences from the source:
--   - generalization: $\mathcal P_i$ chosen with fixed tie-breaking, $h=\lceil C(k+\ell^{10})\rceil$, and $G$ promised $q$-colourable → every minimum-singleton partition, any positive integer $h$, and no colourability (the partition is given); reason: the proof uses only minimality and these properties; the paper's choice is a special case
--   - encoding: the equalities "$=O(h^2)$" and "$=\frac7{25}\Delta+O(h)$" → both the exact bound and a second bound, $c\,h^2$ and $\frac7{25}\Delta+c\,h$, with $c$ depending only on $A$; reason: the $O$ form is an upper bound on the exact one; $\Delta-|K|$ is in $\mathbb R$ so it cannot truncate; Lemma 5.5 supplies the $O$ forms in the proof
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 5.6, p.54 (PDF 56); §5.4, p.53 (PDF 55)

import Mathlib
import Definitions.Def_StreamColour_ACD
import Definitions.Def_StreamColour_Expansion

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 5.6, p.54 (PDF 56), with the construction of §§5.3–5.4.

**Formalization Note.** `X` is an expanded piece: the hypotheses are those of Lemma 5.4 for one index `i`. `P` is **any**
minimum-singleton partition of `X` into at most `q = ∆ − k` classes, not one fixed by tie-breaking. `K` is its singleton core and `D` a
block (a class of size at least two). Each bound is in both forms, the exact one in `ℝ` (where `∆ − |K|` cannot truncate) and the `O` form,
with `c` depending only on `A`. In (ii), the endpoint is named by `∃ z`. -/
theorem lemma_5_6 : ∀ A : ℝ, 0 ≤ A → ∃ c Cs₀ : ℝ, ∀ Cs ≥ Cs₀, ∀ (h n Δ k : ℕ) (G : SimpleGraph (Fin n))
    (π : Fin n → ℕ) (η ε : ℝ) (i : ℕ) (M : Finset (Fin n × Fin n)) (P : Finset (Finset (Fin n))),
    1 ≤ h → 1 ≤ k → k < Δ → 0 < η → 0 < ε → ε < 1 / 100 → (∀ v, (G.neighborSet v).ncard ≤ Δ) →
    IsACD η ε Δ G π → Cs * (h : ℝ) ^ 2 < (Δ : ℝ) →
    1 ≤ i → IsNear A h Δ (piece π i) → IsMaximalCM G (piece π i) M → M.card < 100 * h →
    let X := expanded G Δ (unmatched (piece π i) M)
    IsMinSingleton G X (Δ - k) P →
    let K := singletonCore P
    ∀ D ∈ P, 2 ≤ D.card →
      (3 ≤ D.card →
        (∀ v ∈ D, ∀ u ∈ K, G.Adj v u) ∧
        ((∑ v ∈ D, extDeg G X v : ℕ) : ℝ) ≤ (D.card : ℝ) * ((Δ : ℝ) - (K.card : ℝ)) ∧
        ((∑ v ∈ D, extDeg G X v : ℕ) : ℝ) ≤ c * (h : ℝ) ^ 2) ∧
      ∀ x y, x ≠ y → D = {x, y} →
        (∃ z, (z = x ∨ z = y) ∧ missing G K z ≤ 1) ∧
        ((extDeg G X x : ℝ) + (extDeg G X y : ℝ) ≤
          (7 / 25 : ℝ) * (Δ : ℝ) + (Δ : ℝ) - (K.card : ℝ) + 1) ∧
        ((extDeg G X x : ℝ) + (extDeg G X y : ℝ) ≤ (7 / 25 : ℝ) * (Δ : ℝ) + c * (h : ℝ)) := by sorry

end StreamColour
