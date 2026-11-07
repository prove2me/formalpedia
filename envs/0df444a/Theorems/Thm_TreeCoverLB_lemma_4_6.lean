-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_4_6
-- name    : TreeCoverLB.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:59.799544+00:00
-- url     : https://prove2.me/theorems/22455269-af56-47f6-905d-43f53734fa84
-- title:
--   Lemma 4.6 (labelling form): some simplex has two vertices whose labels differ in every coordinate
-- statement:
--   Let $p$ be prime, $k\ge 2$, $G=\mathbb Z_p$, and suppose there is a continuous $G$-equivariant map $\psi:|I_{p,k}|\to|E_dG|$. Let $r\ge 1$ be an integer and $\Gamma$ a triangulation of the scaled cone $C_r$ over $E_dG$ in which the base is a subcomplex and the $G$-action is simplicial. Let $\ell: V(\Gamma)\to G^k$ satisfy (4.5) on the base:
--   $$
--   \ell(\gamma x)=\ell(x)+(1,\dots,1)\qquad\text{for every vertex } x\in r|E_dG|.
--   $$
--   Then some simplex $\sigma\in\Gamma$ contains vertices $u,v$ with $\ell_j(u)\neq\ell_j(v)$ for every $j\in[k]$.
--
--   In the paper $\ell$ is the vector of winding labels of $k$ dominating trees on $(X_r,d_r)$, which satisfies (4.5).
--
--   Differences from the source:
--   - generalization: the winding labels ℓ_{T_j} of k dominating trees on (X_r, d_r) → any labelling ℓ : V(Γ) → ℤ_p^k satisfying (4.5) on base vertices; reason: the proof uses only (4.5), and the paper's labels satisfy (4.5) (p.15)
--   - generalization: the triangulation Γ_r of Lemma 4.4 → any triangulation of C_r with properties 1–2 of Lemma 4.4; reason: the proof uses only these two properties; Γ_r is one
--   - generalization: for every sufficiently large r → every integer r ≥ 1; reason: the proof does not use the size of r
--   - encoding: d := ind_{ℤ_p}(|I_{p,k}|) with a fixed equivariant ψ → any d with a continuous equivariant ψ : |I_{p,k}| → |E_dℤ_p| as a hypothesis; reason: the paper fixes ψ by Definition 4.2; same hypothesis
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.6, p.15 (PDF p.17), with its proof pp.15–16 and (4.5), p.15

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsAgreementIndexMap
import Definitions.Def_TreeCoverLB_scaledCone
import Definitions.Def_TreeCoverLB_IsTriangulation
import Definitions.Def_TreeCoverLB_IsConeTriangulation

open Classical

namespace TreeCoverLB

/-- **Lemma 4.6** (labelling form) (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.6, p.15 (PDF p.17), with its proof pp.15–16): let
`p` be a prime, `k ≥ 2`, `G = ℤ_p`, and let `ψ : |I_{p,k}| → |E_dG|` be a continuous `G`-equivariant
map. Let `r ≥ 1`, let `Γ` be a triangulation of the cone `C_r` over `E_dG` in which the base `r|K|` is a
subcomplex and the `G`-action is simplicial, and let `ℓ : V(Γ) → G^k` be a labelling that satisfies
(4.5) on the base: `ℓ(γx) = ℓ(x) + (1, …, 1)` for every base vertex `x`. Then some simplex `σ ∈ Γ`
contains vertices `u, v` with `ℓ_j(u) ≠ ℓ_j(v)` for every `j ∈ [k]`.

**Formalization Note** The paper states the lemma for its winding labels `ℓ_{T_j}` of `k` dominating
trees on `(X_r, d_r)`, for the triangulation `Γ_r` of Lemma 4.4 and every sufficiently large `r`.
Its proof uses only properties 1–2 of Lemma 4.4 and the boundary equivariance (4.5) of the labels,
so the statement is posed for every such `Γ`, every `r ≥ 1` and every labelling with (4.5); the
paper's labels satisfy (4.5) (p.15), so the paper's lemma is the special case. Only the values of
`ℓ` on `V(Γ)` matter. -/
theorem lemma_4_6 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (d : ℕ)
    (ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ))
    (hψ : IsAgreementIndexMap p k d ψ) (r : ℕ) (hr : 1 ≤ r)
    (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) (hΓ : IsConeTriangulation p d r Γ)
    (ℓ : (Fin (d + 1) × ZMod p → ℝ) → Fin k → ZMod p)
    (hℓ : ∀ x ∈ vertexSet Γ, x ∈ coneBase (EJoin d (ZMod p)) r →
      ℓ (ejoinAct (1 : ZMod p) x) = ℓ x + fun _ => 1) :
    ∃ σ ∈ Γ, ∃ u ∈ σ, ∃ v ∈ σ, ∀ j : Fin k, ℓ u j ≠ ℓ v j := by sorry

end TreeCoverLB
