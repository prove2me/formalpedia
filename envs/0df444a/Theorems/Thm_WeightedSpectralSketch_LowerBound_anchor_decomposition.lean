-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_anchor_decomposition
-- name    : WeightedSpectralSketch.LowerBound.anchor_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:13:06.895266+00:00
-- url     : https://prove2.me/theorems/e997d2fa-aa6b-4078-914c-3d7331015792
-- title:
--   Lemma 6.3 — decomposing an arbitrary sketch into an incidence sketch plus anchor columns
-- statement:
--   Let $C\subseteq V$ be an anchor set with ring $R=V\setminus C$, and let $A=[a_e]$ be any real sketch matrix with $N$ rows. There exist an incidence sketch matrix $B=[b_e:e\in\binom R2]$ on $R$ of dimension $K(C)$, a matrix $T\in\mathbb R^{N\times K(C)}$ and vectors $(c_e)_{e\in\binom R2}$ in $\mathbb R^{\binom C2}$, all determined by $A$ and $C$, such that
--
--   1. for every anchor-good ring edge $e$, $a_e=T\,b_e+A_C\,c_e$ and $\|c_e\|_2^2\le3$;
--   2. for every ring edge $e$ that is not anchor-good, $b_e=0$ and $c_e=0$.
--
--   This converts the analysis of an arbitrary sketch into that of an incidence sketch on the ring (Lemma 5.2), at the price of an anchor residual.
--
--   **Formalization Note.** The ring is the subtype of vertices outside $C$; a ring edge is mapped to the corresponding column of $A$ by `liftEdge`. Since $A$ and $C$ are fixed, the existential quantifier expresses "determined by $A$ and $C$".
--
--   Differences from the source:
--
--   - generalization: any realization of the anchor C and ring R of the anchored template (|C| = |R| = ℓb) → any subset C of a finite vertex type, with R its complement; reason: the source's realizations are the subsets of size ℓb, an instance
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 23, Lemma 6.3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Anchor

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 6.3, p. 23: for any anchor set `C ⊆ V` (ring `R = V \ C`) and any sketch matrix `A`
there are an incidence sketch matrix `B = [b_e : e ∈ binom(R,2)]` on `R` of dimension `K(C)`, a
matrix `T ∈ ℝ^{N × K(C)}` and vectors `c_e ∈ ℝ^{binom(C,2)}`, all determined by `A` and `C`, with
(1) `a_e = T b_e + A_C c_e` and `‖c_e‖₂² ≤ 3` for every anchor-good ring edge `e`, and
(2) `b_e = 0` and `c_e = 0` for every ring edge `e` that is not anchor-good. -/
theorem anchor_decomposition {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V) :
    ∃ (B : Matrix (Fin (KDim A C)) (EdgeSlot {v // v ∉ C}) ℝ)
      (T : Matrix (Fin N) (Fin (KDim A C)) ℝ)
      (c : EdgeSlot {v // v ∉ C} → anchorEdges C → ℝ),
      IsIncidence B ∧
      (∀ e, AnchorGood A C (liftEdge C e).1 →
        Aᵀ (liftEdge C e) = T *ᵥ Bᵀ e + anchorMat A C *ᵥ c e ∧ ∑ k, c e k ^ 2 ≤ 3) ∧
      (∀ e, ¬ AnchorGood A C (liftEdge C e).1 → Bᵀ e = 0 ∧ c e = 0) := by sorry

end WeightedSpectralSketch.LowerBound
