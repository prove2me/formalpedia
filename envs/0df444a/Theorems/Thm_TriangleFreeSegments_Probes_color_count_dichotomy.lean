-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_color_count_dichotomy
-- name    : TriangleFreeSegments.Probes.color_count_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:06.639786+00:00
-- url     : https://prove2.me/theorems/d2133a93-939b-499d-8849-e68b03e30f16
-- title:
--   Proof of Lemma 2, p. 4 — differing color sets give k + 1 colors on their union; equal ones force a new color on the diagonal, k + 1 with it
-- statement:
--   Let $(F_i)_{i\in I}$ be a finite indexed family of plane sets, with intersection graph $G$ (two distinct indices are adjacent when their sets intersect), and let $\phi$ be a proper coloring of $G$ with colors in an arbitrary set. Let $k\in\mathbb N$, let $X,Y\subseteq I$ be sets of indices on which $\phi$ uses at least $k$ colors each, $|\phi(X)|\ge k$ and $|\phi(Y)|\ge k$, and let $D\in I$ be adjacent to every member of $Y$. Then:
--
--   1. if $\phi(X)\neq\phi(Y)$, then $\phi$ uses at least $k+1$ colors on $X\cup Y$;
--   2. if $\phi(X)=\phi(Y)$, then $D$ receives a color not used on $Y$, and
--   $$
--   |\phi(X\cup\{D\})|\ge k+1 .
--   $$
--
--   In the proof of Lemma 2, $X$ is the set $\mathcal S(P)$ of segments meeting a probe $P$, $Y$ the set $\mathcal S_P(Q)$ of segments of the inner copy meeting a probe $Q$, and $D$ the diagonal $D_Q$, which crosses every segment of $\mathcal S_P(Q)$. The lower probe $L_Q$ meets $\mathcal S(P)\cup\mathcal S_P(Q)$ and the upper probe $U_Q$ meets $\mathcal S(P)\cup\{D_Q\}$, so this case split is where the count $k+1$ of the induction step comes from.
--
--   **Formalization Note.** The statement abstracts from the construction: $X$, $Y$, $D$ are arbitrary, and the geometric facts the page uses (which segments $L_Q$, $U_Q$ meet; $D_Q$ crossing $\mathcal S_P(Q)$) enter as the adjacency hypothesis on $D$. The index type is finite so that the color counts (`Set.ncard`) are genuine.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, p. 4, proof of Lemma 2, last two sentences of the proof

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem color_count_dichotomy {ι α : Type} [Finite ι] (F : ι → Set (ℝ × ℝ)) (φ : ι → α)
    (hφ : ∀ i j, (interGraph F).Adj i j → φ i ≠ φ j) (k : ℕ) (X Y : Set ι) (D : ι)
    (hD : ∀ i ∈ Y, (interGraph F).Adj D i)
    (hX : k ≤ (φ '' X).ncard) (hY : k ≤ (φ '' Y).ncard) :
    (φ '' X ≠ φ '' Y → k + 1 ≤ (φ '' (X ∪ Y)).ncard) ∧
    (φ '' X = φ '' Y → φ D ∉ φ '' Y ∧ k + 1 ≤ (φ '' (insert D X)).ncard) := by sorry

end TriangleFreeSegments.Probes
