-- Prove2me | Theorems.Thm_SP4Mission_local_homology_zero
-- name    : SP4Mission.local_homology_zero
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-12T22:20:30.782972+00:00
-- url     : https://prove2.me/theorems/df63a976-ad04-416a-960d-1ff976db3104
-- title:
--   Local homology of an $n$-manifold: $H_k(M, M\setminus\{p\};\mathbb Z)=0$ for $k\ne n$
-- statement:
--   Let $M$ be a Hausdorff topological $n$-manifold (a space with an atlas modelled on $\mathbb R^n$) and $p\in M$. Then the local homology groups of $M$ at $p$ vanish in all degrees other than $n$:
--
--   $$
--   H_k\big(M, M\setminus\{p\};\mathbb Z\big)=0\qquad\text{for all } k\ne n .
--   $$
--
--   (In degree $n$ the group is $\mathbb Z$.) By excision, $H_k(M,M\setminus\{p\})\cong H_k(U,U\setminus\{p\})$ for a coordinate neighbourhood $U\cong\mathbb R^n$ of $p$, and the long exact sequence of the pair $(\mathbb R^n,\mathbb R^n\setminus\{0\})$ together with the contractibility of $\mathbb R^n$ and $\mathbb R^n\setminus\{0\}\simeq S^{n-1}$ gives $H_k(\mathbb R^n,\mathbb R^n\setminus\{0\})\cong\tilde H_{k-1}(S^{n-1})$, which is $\mathbb Z$ for $k=n$ and $0$ otherwise. This is the computation by which the dimension of a manifold is seen to be a topological invariant, and it supplies the relative groups in the long exact sequence of the pair $(M,M\setminus\{p\})$ used in the mission.
--
--   **Formalization Note** The pair is given by the inclusion `Subtype.val : {x : M // x ≠ p} → M`, relative homology is `SP4Homology.Hrel`, and vanishing is `IsZero` in `ModuleCat ℤ`. The statement holds for all $n\ge0$ and needs neither compactness nor connectedness of $M$; the Hausdorff hypothesis is part of the definition of a manifold.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §3.3, p. 231: "for x ∈ M, the local homology group Hᵢ(M, M − {x}; Z) is nonzero only for i = n: Hᵢ(M, M − {x}; Z) ≈ Hᵢ(Rⁿ, Rⁿ − {0}; Z) by excision ≈ H̃ᵢ₋₁(Rⁿ − {0}; Z) ≈ H̃ᵢ₋₁(Sⁿ⁻¹; Z)"; also §2.1, p. 126 (local homology groups Hₙ(X, X − {x}) and excision, Theorem 2.20, p. 119).

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap
import Definitions.Def_SP4RelHomology

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.local_homology_zero (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) (k : ℕ) (hk : k ≠ n) :
    IsZero (SP4Homology.Hrel k
      (⟨Subtype.val, continuous_subtype_val⟩ : C({x : M // x ≠ p}, M))) := by sorry
