-- Prove2me | Theorems.Thm_SP4Mission_compl_singleton_simplyConnectedAtInfinity
-- name    : SP4Mission.compl_singleton_simplyConnectedAtInfinity
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T05:09:06.944719+00:00
-- url     : https://prove2.me/theorems/43ff6f98-281c-432d-8202-650f37b1d2d1
-- title:
--   The complement of a point in a compact $n$-manifold, $n\ge3$, is simply connected at infinity
-- statement:
--   Let $n\ge3$ and let $M$ be a compact Hausdorff space with a charted-space structure modeled on $\mathbb R^n$, so that $M$ is a closed topological $n$-manifold, not necessarily connected. Then for every point $p\in M$ the punctured manifold $M\setminus\{p\}$ is simply connected at infinity in Freedman's sense: for every compact $K\subseteq M\setminus\{p\}$ there is a compact $L$ with $K\subseteq L\subseteq M\setminus\{p\}$ such that every loop in $(M\setminus\{p\})\setminus L$ contracts in $(M\setminus\{p\})\setminus K$. In symbols,
--
--   $$
--   M\ \text{a compact } n\text{-manifold},\ n\ge3,\ p\in M\quad\Longrightarrow\quad M\setminus\{p\}\ \text{is simply connected at infinity}.
--   $$
--
--   The end of $M\setminus\{p\}$ is a punctured coordinate ball around $p$, and punctured Euclidean space $\mathbb R^n\setminus\{0\}\simeq S^{n-1}$ is simply connected for $n\ge3$. This is the property that makes the hypothesis of Freedman's proper $h$-cobordism theorem — simple connectivity at infinity of the punctured manifolds $M-\mathrm{pt}$ — available for closed $4$-manifolds in his proof of Theorem 1.5, and it is the third condition of the criterion attached to Corollary 1.2 when that corollary is applied to a punctured homotopy sphere. The statement is false for $n\le2$ (for example $S^2\setminus\{p\}\cong\mathbb R^2$ is not simply connected at infinity), which is why $n\ge3$ is required. Connectedness of $M$ is not needed, since the compact set $L$ may be taken to contain every component of $M$ other than the one containing $p$.
--
--   **Formalization Note** `SP4Ends.SimplyConnectedAtInfinity` is Freedman's definition with based null-homotopies (`Path.Homotopic` in the subtype `Kᶜ`). The manifold hypothesis is only a topological atlas `ChartedSpace (EuclideanSpace ℝ (Fin n)) M`, and the statement is uniform in the dimension `n` with the hypothesis `3 ≤ n`.
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf). Definition: Note after Theorem 10.3, p. 436 ("A space X is simply connected at infinity if given any compactum K₁ ⊂ X there exists a larger compactum K₂ ⊂ X, K₁ ⊂ K₂, such that every loop in X − K₂ contracts in X − K₁"). Use for punctured closed 4-manifolds: proof of Theorem 1.5 (uniqueness), p. 369: "It is easily seen that (W; M′ − pt, M − pt) is a (topological) proper h-cobordism which is 1-connected and simply connected at infinity"; Corollary 1.2, p. 366, condition (3) of the criterion for V ≃_p R⁴, applied to V = Σ⁴ − pt. The underlying fact that Sⁿ⁻¹, hence Rⁿ − {0}, is simply connected for n ≥ 3: A. Hatcher, Algebraic Topology, Cambridge University Press, 2002, Proposition 1.14 (π₁(Sⁿ) = 0 for n ≥ 2). Reduction child of SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4Ends

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.compl_singleton_simplyConnectedAtInfinity
    (n : ℕ) (hn : 3 ≤ n) (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    SP4Ends.SimplyConnectedAtInfinity {x : M // x ≠ p} := by sorry
