-- Prove2me | Theorems.Thm_SP4Mission_punctured_closed_manifold_homology
-- name    : SP4Mission.punctured_closed_manifold_homology
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-09T02:57:53.946526+00:00
-- url     : https://prove2.me/theorems/a5d8057d-2859-47e4-909f-70ac87f35459
-- title:
--   Homology of a punctured closed simply connected $n$-manifold
-- statement:
--   Let $M$ be a closed (compact Hausdorff) topological $n$-manifold which is simply connected, let $p\in M$ and $V:=M\setminus\{p\}$. Then the inclusion $\iota\colon V\hookrightarrow M$ induces isomorphisms
--
--   $$
--   \iota_*\colon H_k(V;\mathbb Z)\xrightarrow{\ \cong\ }H_k(M;\mathbb Z)\qquad\text{for all } k\ne n,
--   $$
--
--   and the top homology of the punctured manifold vanishes, $H_n(V;\mathbb Z)=0$.
--
--   This is the classical computation of the homology of a punctured closed orientable manifold. The long exact sequence of the pair $(M,V)$ reads $\cdots\to H_k(V)\to H_k(M)\to H_k(M,V)\to H_{k-1}(V)\to\cdots$, and by excision the relative groups are the local homology groups $H_k(M,V)=H_k(M,M\setminus\{p\})\cong H_k(\mathbb R^n,\mathbb R^n\setminus\{0\})\cong\tilde H_{k-1}(S^{n-1})$, which vanish for $k\ne n$ and equal $\mathbb Z$ for $k=n$. Hence $\iota_*$ is an isomorphism in all degrees $k\notin\{n-1,n\}$. In the remaining degrees one uses that $M$ is orientable — a simply connected manifold is orientable (Hatcher, Proposition 3.25) — so that the map $H_n(M)\to H_n(M,M\setminus\{p\})\cong\mathbb Z$ is an isomorphism (Hatcher, Theorem 3.26(a)); exactness then gives $H_n(V)\to H_n(M)$ zero and injective, i.e. $H_n(V)=0$, and $H_{n-1}(V)\to H_{n-1}(M)$ an isomorphism. The orientability hypothesis is necessary in degree $n-1$: for $M=\mathbb{RP}^2$ the punctured surface is a Möbius band with $H_1=\mathbb Z$, while $H_1(\mathbb{RP}^2)=\mathbb Z/2$. In the mission the statement is applied to a homotopy $4$-sphere $M$ and gives $H_4(M\setminus\{p\})=0$ and $H_k(M\setminus\{p\})\cong H_k(M)$ for $k\ne4$.
--
--   **Formalization Note** The manifold hypothesis is a topological atlas `ChartedSpace (EuclideanSpace ℝ (Fin n)) M` with `T2Space M` and `CompactSpace M`; simple connectivity is Mathlib's `SimplyConnectedSpace M` and is used only to guarantee orientability, for which Mathlib has no definition. The punctured manifold is the subtype `{x : M // x ≠ p}`, the inclusion is the continuous map `Subtype.val`, and "induces an isomorphism" is `IsIso (SP4Homology.map k ι)` in `ModuleCat ℤ`. The statement covers all $n\ge0$ (for $n\le1$ it is trivial or vacuous).
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, Theorem 2.16, p. 117 (long exact sequence of a pair), Theorem 2.20, p. 119 (excision), p. 126 (local homology groups Hₙ(X, X − {x}) and their excision property), §3.3, p. 231 (Hᵢ(M, M − {x}; Z) ≈ Hᵢ(Rⁿ, Rⁿ − {0}; Z) ≈ H̃ᵢ₋₁(Rⁿ − {0}; Z), nonzero only for i = n), Proposition 3.25, p. 234 (a simply-connected manifold is orientable), and Theorem 3.26(a), p. 236 (for a closed connected R-orientable n-manifold, Hₙ(M; R) → Hₙ(M | x; R) ≈ R is an isomorphism for all x).

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.punctured_closed_manifold_homology
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    (∀ k : ℕ, k ≠ n →
        IsIso (SP4Homology.map k (⟨Subtype.val, continuous_subtype_val⟩ : C({x : M // x ≠ p}, M)))) ∧
      IsZero (SP4Homology.H n {x : M // x ≠ p}) := by sorry
