-- Prove2me | Theorems.Thm_SP4Mission_smooth_contractible_scAtInfinity_homeomorph_euclidean
-- name    : SP4Mission.smooth_contractible_scAtInfinity_homeomorph_euclidean
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-08T05:08:52.37485+00:00
-- url     : https://prove2.me/theorems/2e864405-352d-43c4-9937-21d3ba706100
-- title:
--   Freedman — a smooth contractible four-manifold that is simply connected at infinity is homeomorphic to $\mathbb R^4$
-- statement:
--   This is the smooth case of the four-dimensional instance of the Stallings–Freedman characterization of Euclidean space, and precisely the second half of the proof of Freedman's Corollary 1.2, the half that follows the smoothing step.
--
--   Let $V$ be a Hausdorff, second countable topological space with a $C^\infty$ atlas modeled on $\mathbb R^4$, that is, a smooth $4$-manifold without boundary. Assume that $V$ is contractible and that $V$ is simply connected at infinity: for every compact $K\subseteq V$ there is a compact $L\supseteq K$ such that every loop in $V\setminus L$ contracts in $V\setminus K$. Then
--
--   $$
--   V\;\cong_{\mathrm{Top}}\;\mathbb R^4 .
--   $$
--
--   The conclusion is a homeomorphism only. No diffeomorphism is asserted, and none can be in general: the exotic $\mathbb R^4$'s are smooth manifolds satisfying these hypotheses that are not diffeomorphic to $\mathbb R^4$. Contractibility forces $V$ to be nonempty, connected and noncompact. The smooth hypothesis is exactly what the smoothing theorem for connected noncompact $4$-manifolds provides, so Corollary 1.2 in its topological form (any topological $4$-manifold proper-homotopy equivalent to $\mathbb R^4$ is homeomorphic to $\mathbb R^4$) follows by combining that theorem with the present statement. In Guilbault's formulation: a contractible open $n$-manifold, $n\ge3$, is homeomorphic to $\mathbb R^n$ if and only if it is simply connected at infinity, the case $n=4$ being Freedman's.
--
--   **Formalization Note** The smooth structure is the pair of instances `ChartedSpace (EuclideanSpace ℝ (Fin 4)) V` and `IsManifold (𝓡 4) ∞ V`; contractibility is Mathlib's `ContractibleSpace V`; simple connectivity at infinity is `SP4Ends.SimplyConnectedAtInfinity V`, Freedman's definition with based null-homotopies. The conclusion is `Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 4))`.
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf). Corollary 1.2, p. 366: "Any topological 4-manifold V which is proper-homotopy equivalent to R⁴ is homeomorphic to R⁴. (The assumption V ≃_p R⁴ is equivalent to requiring: (1) π₁(V) = 0, H₂(V; Z) = 0, and V simply connected at infinity. For this see Larry Siebenmann's Bourbaki seminar [48].)" Its proof, p. 366: smoothing theory gives a smoothing V_Σ of V; "By hand one can construct a proper-h-cobordism W between V_Σ and R⁴. Set (W; V_Σ, R⁴) = (V_Σ × [0,1) ∪ B⁴ × 1; V_Σ × 0, B⁴ × 1) where B⁴ is the interior of a smooth 4-ball in V_Σ. Now apply Theorem 10.4 to obtain R⁴ =_Top V_Σ =_Top V." The present statement is this second half of the proof, with the smoothing V_Σ taken as hypothesis and contractibility (which implies (1) and (2)) in place of (1)–(2). Theorem 10.3 (proper h-cobordism theorem), pp. 435–436. Modern formulation: C. R. Guilbault, Ends, shapes, and boundaries in manifold topology and geometric group theory, in: Topology and Geometric Group Theory, Springer Proc. Math. Stat. 184 (2016), 45–125, arXiv:1210.6741, Theorem 3.5.3 ("Stallings' Characterization of Rⁿ": a contractible open n-manifold, n ≥ 3, is homeomorphic to Rⁿ if and only if it is simply connected at infinity; the case n = 4 attributed to Freedman [Free82]). Reduction child of SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4Ends

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.smooth_contractible_scAtInfinity_homeomorph_euclidean
    (V : Type*) [TopologicalSpace V] [T2Space V] [SecondCountableTopology V]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) V] [IsManifold (𝓡 4) ∞ V]
    [ContractibleSpace V] (hV : SP4Ends.SimplyConnectedAtInfinity V) :
    Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 4)) := by sorry
