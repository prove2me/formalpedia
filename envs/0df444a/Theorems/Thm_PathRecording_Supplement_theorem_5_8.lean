-- Prove2me | Theorems.Thm_PathRecording_Supplement_theorem_5_8
-- name    : PathRecording.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:33:27.602575+00:00
-- url     : https://prove2.me/theorems/e9b8bbd4-36de-4c9c-ad24-a2f6af4e5fbf
-- title:
--   Theorem 5.8 — transpose path-recording update: $Q_{\rho^\top}(|x\rangle\otimes\Theta_t)=\sum_y|y\rangle\otimes\Theta_{t+1}\mathrm{App}^{(t)}_{y,x}$
-- statement:
--   Let $G$ be a compact group with its normalized Haar measure and $\rho:G\to U(N)$ a continuous unitary representation, and let $Q_{\rho^\top}$ be the purified oracle that applies $\rho(g)^\top$ (transpose in the fixed basis $B(V)$) to the query register:
--   $$Q_{\rho^\top}\Big(|x\rangle\otimes\int_G f(g)|g\rangle\,dg\Big)=\int_G f(g)\,\rho(g)^\top|x\rangle\otimes|g\rangle\,dg .$$
--   1. For every $t\ge0$ and every $x\in B(V)$,
--   $$Q_{\rho^\top}\cdot(|x\rangle\otimes\Theta_t)=\sum_{y\in B(V)}|y\rangle\otimes\Theta_{t+1}\,\mathrm{App}^{(t)}_{y,x},$$
--   as an identity of maps on $\mathrm{Path}_t$, where $\Theta_t|\vec x,\vec y\rangle=\int_G\langle\vec y|\rho(g)^{\otimes t}|\vec x\rangle|g\rangle\,dg$ and $\mathrm{App}^{(t)}_{y,x}$ appends the reversed pair $(y,x)$.
--   2. Consequently, for every family of Schur–Weyl data and every $t$, with $Q^{\mathrm{Path},\top}_{\rho,t+1}=\sum_{x,y}|y\rangle\langle x|\otimes W_{t+1}\Omega_{\mathcal A_{t+1}}\mathrm{App}^{(t)}_{y,x}W_t^+\Omega_{\mathcal A_t}$,
--   $$Q^{\mathrm{Path},\top}_{\rho,t+1}\cdot(I_V\otimes\Gamma_tF)=(I_V\otimes\Gamma_{t+1}F)\cdot Q_{\rho^\top}$$
--   on inputs in $V\otimes F^{-1}(\mathrm{Tab}_t)$.
--
--   Adaptive algorithms making forward and transpose queries are therefore simulated by the path-recording oracle, appending $(x,y)$ for a forward query and $(y,x)$ for a transpose query.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized bi-invariant Haar measure of Definition 3.1
--   - encoding: V ⊗ L²(G) with Q_M(|x⟩⊗|f⟩) = ∫ f(g) M(g)|x⟩⊗|g⟩ dg → functions from the basis of V to Lp ℂ 2 μ, with (Q_M φ)_y = Σ_x M(·)_{yx} · φ_x (matrix entries as L^∞ multipliers); reason: Eq. (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^{dim V}
--   - encoding: Q^{Path,⊤}_{ρ,t+1}·(I_V⊗Γ_tF) = (I_V⊗Γ_{t+1}F)·Q_{ρ⊤} on inputs restricted to V⊗F⁻¹(Tab_t) → for every family of Schur–Weyl data and every φ : Fin N → L²(G) with every component in matrixCoeffSpace (the span of F⁻¹|λ,X,Y⟩, λ ∈ Ĝ_t), the vector (x,p) ↦ (Γ_{t+1}F(Q_{ρ⊤}φ)_x)_p equals Q^{Path,⊤}_{ρ,t+1} applied to (x,p) ↦ (Γ_tFφ_x)_p; reason: the base mission's encoding of the first claim of Theorem 5.3 (PathRecording.first_claim), with Γ_tF the published gammaF
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 5.8, pp.67–68

import Mathlib
import Definitions.Def_PathRecording_fourier
import Definitions.Def_PathRecording_pathOracle
import Definitions.Def_PathRecording_Supplement_matOracle
import Definitions.Def_PathRecording_Supplement_pathOracleT

set_option autoImplicit false

namespace PathRecording.Supplement

open Matrix MeasureTheory

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 5.8 (Transpose path-recording update), pp.67–68. Let `Q_{ρ⊤}` apply
`ρ(g)⊤` (transpose in the fixed basis `B(V)`) to the query register. Then
1. for every `x ∈ B(V)`, `Q_{ρ⊤}(|x⟩ ⊗ Θ_t) = Σ_{y∈B(V)} |y⟩ ⊗ Θ_{t+1} App^{(t)}_{y,x}`, as an
   identity on every `v ∈ Path_t`;
2. for every family of Schur–Weyl data and every `t`,
   `Q^{Path,⊤}_{ρ,t+1} (I_V ⊗ Γ_t F) = (I_V ⊗ Γ_{t+1} F) Q_{ρ⊤}` on inputs in `V ⊗ F⁻¹(Tab_t)`.

**Formalization Note.** `Q_{ρ⊤}` is `matOracle μ (transposeMap ρ)`: `(Q_{ρ⊤}φ)_y = Σ_x ⟨x|ρ(·)|y⟩ φ_x`.
`App^{(t)}_{y,x}` is the published `append t y x` (the reversed pair). A state of
`V ⊗ F⁻¹(Tab_t)` is `φ : Fin N → L²(G)` with every component in `matrixCoeffSpace μ (S t)`;
`(I_V ⊗ Γ_t F)φ` is `(x, p) ↦ (Γ_t F φ_x)_p` (published `gammaF`), exactly as in
`PathRecording.first_claim`. -/
theorem theorem_5_8 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (ρ : UnitaryRep G N) :
    (∀ (t : ℕ) (x : Fin N) (v : PathIdx N t → ℂ),
        matOracle μ (transposeMap ρ) (Pi.single x (theta μ ρ t v)) =
          fun y => theta μ ρ (t + 1) (append t y x *ᵥ v)) ∧
    (∀ (S : (t : ℕ) → SchurWeylData ρ t) (t : ℕ) (φ : Fin N → Lp ℂ 2 μ),
        (∀ x, φ x ∈ matrixCoeffSpace μ (S t)) →
        (fun q : Fin N × PathIdx N (t + 1) =>
            gammaF μ (S (t + 1)) (matOracle μ (transposeMap ρ) φ q.1) q.2) =
          pathOracleT (S t) (S (t + 1)) *ᵥ
            fun q : Fin N × PathIdx N t => gammaF μ (S t) (φ q.1) q.2) := by sorry

end PathRecording.Supplement
