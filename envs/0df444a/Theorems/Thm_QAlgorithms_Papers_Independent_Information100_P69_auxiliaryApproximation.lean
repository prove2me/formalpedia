-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_auxiliaryApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P69.auxiliaryApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:56:06.410787+00:00
-- url     : https://prove2.me/theorems/b50a40c5-eef1-498b-aae6-eae86558c0dd
-- title:
--   Testing and auxiliary map approximation
-- statement:
--   Fix Stinespring isometries $V:H\to K\otimes E$ and $W:H\to K\otimes F$ of channels $T$ and $M$. Let $h_t(T\|M)=\sup_{\psi,Q}(p-tq)$, where $p,q$ are their acceptance probabilities for the same normalized reference-assisted input and effect. For every $t\ge0$ there is one map $A:F\to E$ such that
--   $$\|A\|_\infty\le\sqrt t,\qquad\|V-(I_K\otimes A)W\|_\infty^2\le h_t(T\|M).$$
--   If a CPTP map $L\le_{\rm CP}tM$ obeys $\|L-T\|_\diamond\le\delta$, the same squared error is at most $\delta/2$; exact domination permits zero error. Conversely, for every auxiliary map, the map induced by $(I_K\otimes A)W$ is CP-dominated by $\|A\|_\infty^2M$. This is a uniform auxiliary-map estimate; the source credits its approximation estimate to [10, Proposition 4.2].
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 10, Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 6, prescribed dilation spaces and uniform auxiliary map, PDF pp.10–11.
The approximation estimate is credited there to [10, Proposition 4.2]. -/
theorem auxiliaryApproximation [Nonempty A] [Nonempty B] {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
    [DecidableEq F] [Nonempty E] [Nonempty F]
    (V : Matrix (B × E) A ℂ) (W : Matrix (B × F) A ℂ)
    (hV : V.conjTranspose * V = 1) (hW : W.conjTranspose * W = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ D : Matrix E F ℂ, specNorm D ≤ Real.sqrt t ∧
      specNorm (V - Matrix.kronecker (1 : Matrix B B ℂ) D * W)^2 ≤
        testingTail (dilationMap V) (dilationMap W) t ∧
      (∀ L : Superop A B, IsChannel L → CPLe L ((t:ℂ) • dilationMap W) →
        ∀ delta : ℝ, diamond (L-dilationMap V) ≤ delta →
          specNorm (V-Matrix.kronecker (1 : Matrix B B ℂ) D*W)^2 ≤ delta/2) ∧
      (CPLe (dilationMap V) ((t:ℂ) • dilationMap W) →
        V = Matrix.kronecker (1 : Matrix B B ℂ) D*W) ∧
      (∀ D0 : Matrix E F ℂ, CPLe (dilationMap (Matrix.kronecker (1 : Matrix B B ℂ) D0*W))
        ((((specNorm D0)^2:ℝ):ℂ) • dilationMap W)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
