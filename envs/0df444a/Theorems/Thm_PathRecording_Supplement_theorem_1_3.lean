-- Prove2me | Theorems.Thm_PathRecording_Supplement_theorem_1_3
-- name    : PathRecording.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:31:53.781926+00:00
-- url     : https://prove2.me/theorems/d705934f-a839-4c4c-97e0-f422253ce34a
-- title:
--   Theorem 1.3 — conjugate, transpose and inverse tableau queries from one forward query
-- statement:
--   Let $G$ be a compact group with its normalized Haar measure, $\widehat G$ the complete catalogue of its irreducible representations with dual labels $\lambda\mapsto\lambda^*$ and unitaries $J_\lambda$ with $\overline{\rho_\lambda(g)}=J_\lambda\rho_{\lambda^*}(g)J_\lambda^\dagger$, and $\rho:G\to U(N)$ a continuous unitary representation on $V=\mathbb C^N$. Write $F^{-1}:\mathrm{Tab}(\widehat G)\to L^2(G)$ for the inverse Fourier transform, $K$ for complex conjugation of coordinates in the basis $|x\rangle\otimes|\lambda,X,Y\rangle$, $\overline T=KTK$, $\mathrm{Sw}:|\lambda,X,Y\rangle\mapsto|\lambda,Y,X\rangle$, and $D_J:|\lambda,X,Y\rangle\mapsto\sum_{X',Y'}\overline{(J_\lambda)_{XX'}}(J_\lambda)_{YY'}|\lambda^*,X',Y'\rangle$.
--
--   Let $T$ be any map on $V\otimes\mathrm{Tab}(\widehat G)$ that preserves square-summability and satisfies $Q_\rho\,(I\otimes F^{-1})=(I\otimes F^{-1})\,T$ on square-summable inputs, so that $T$ is the tableau oracle $Q^{\mathrm{Tab}}_\rho$. Then on every square-summable input
--   $$Q_{\rho^\top}(I\otimes F^{-1})=(I\otimes F^{-1})\,(I\otimes\mathrm{Sw})\,\overline T\,(I\otimes\mathrm{Sw}),$$
--   $$Q_{\rho^*}(I\otimes F^{-1})=(I\otimes F^{-1})\,(I\otimes D_J)\,\overline T\,(I\otimes\overline{D_J}),$$
--   $$Q_{\rho^\dagger}(I\otimes F^{-1})=(I\otimes F^{-1})\,(I\otimes D_J\mathrm{Sw})\,T\,(I\otimes D_J\mathrm{Sw}).$$
--   That is, $Q^{\mathrm{Tab}}_{\rho^\top}$, $Q^{\mathrm{Tab}}_{\rho^*}$ and $Q^{\mathrm{Tab}}_{\rho^\dagger}$ are each implemented by one application of $Q^{\mathrm{Tab}}_\rho$ (or of its complex conjugate) with pre- and post-processing that depends only on $\widehat G$ and $J$.
--
--   This gives simulators for all four query types $\rho(g)$, $\rho(g)^\top$, $\rho(g)^*$, $\rho(g)^\dagger$ from any implementation of the forward tableau oracle.
--
--   **Formalization Note** Square-summable inputs are families with every component in $\ell^2$; $F^{-1}$ is the series of `PathRecording.Supplement.GHat`. The Haar measure is required to be regular (Definition 3.1), so that inversion preserves it.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized (regular, bi-invariant) Haar measure dg → G any compact topological group with a Borel σ-algebra and a regular left Haar probability measure μ; reason: the Lie structure is never used; on a compact group a regular left Haar probability measure is the normalized bi-invariant Haar measure of Definition 3.1, which is inversion invariant
--   - encoding: V ⊗ L²(G) with Q_M(|x⟩⊗|f⟩) = ∫ f(g) M(g)|x⟩⊗|g⟩ dg → functions from the basis of V to Lp ℂ 2 μ, with (Q_M φ)_y = Σ_x M(·)_{yx} · φ_x (matrix entries as L^∞ multipliers); reason: Eq. (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^{dim V}
--   - encoding: Tab(Ĝ) = ⨁_λ V_λ ⊗ V_λ* with the Fourier transform F of Peter–Weyl (Theorem 3.6) → square-summable coefficient functions on the basis |λ,X,Y⟩ of a complete irrep catalogue Ĝ, with F⁻¹ given by the series Σ w_{λXY} √d_λ ⟨Y|ρ_λ(·)|X⟩; reason: Peter–Weyl is cited, not proved; F is unitary, so F⁻¹ determines it
--   - encoding: we can implement Q^Tab_{ρ*}, Q^Tab_{ρ⊤}, Q^Tab_{ρ†} each with a single application of Q^Tab_ρ and simple pre- and post-processing → three intertwining identities Q_{ρ⊤}(I⊗F⁻¹) = (I⊗F⁻¹)(I⊗Sw)T̄(I⊗Sw), Q_{ρ*}(I⊗F⁻¹) = (I⊗F⁻¹)(I⊗D_J)T̄(I⊗D̄_J), Q_{ρ†}(I⊗F⁻¹) = (I⊗F⁻¹)(I⊗D_J Sw)T(I⊗D_J Sw) on square-summable inputs; reason: these are the implementations of §4.2.2 and footnote 9; Q^Tab_M = (I⊗F)Q_M(I⊗F)⁻¹ with F unitary, so intertwining with F⁻¹ is equality with Q^Tab_M
--   - generalization: black-box access to Q^Tab_ρ = (I⊗F)Q_ρ(I⊗F)⁻¹ → any map T on V⊗Tab(Ĝ) that preserves square-summability and satisfies Q_ρ(I⊗F⁻¹) = (I⊗F⁻¹)T on square-summable inputs; reason: F⁻¹ is injective (Lemma 3.8), so every such T equals Q^Tab_ρ on Tab(Ĝ); the black box is one such T
--   - generalization: V_{λ*} identified non-canonically with V_λ* so that ρ_{λ*}(g) = ρ_λ(g)* in the chosen basis (pp.33, 38), and the relabelling |λ,X,Y⟩ ↦ |λ*,X,Y⟩ → any unitary J_λ with conj(ρ_λ(g)) = J_λ ρ_{λ*}(g) J_λ† and the map D_J|λ,X,Y⟩ = Σ conj((J_λ)_{XX'})(J_λ)_{YY'}|λ*,X',Y'⟩; reason: J_λ = I is the paper's case, where D_J is the relabelling; J_λ = I is impossible for a self-dual quaternionic irrep (SU(2)'s defining one), and D_J is the 'bijective mapping between the labels and bases' of p.9
--   - reading: §4.2.2, p.52: transpose queries use Q^Tab_ρ conjugated by |λ,X,Y⟩ ↦ |λ,Y,X⟩ (no complex conjugate) → transpose queries use the complex conjugate T̄ = KTK conjugated by Sw; reason: footnote 9 of Theorem 1.3 says transpose and conjugate queries need the complex conjugate of Q^Tab_ρ; Transpose is antilinear (p.33), and Transpose f(g) = conj f(g⁻¹) gives Q^Tab_{ρ⊤} = Sw·conj(Q^Tab_ρ)·Sw; for real-coefficient Q^Tab_ρ the two agree
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 1.3, p.9, footnote 9; proof in §4.2.2, pp.51–52, using §3.3.1, p.33

import Mathlib
import Definitions.Def_PathRecording_fourier
import Definitions.Def_PathRecording_Supplement_matOracle
import Definitions.Def_PathRecording_Supplement_DualData

set_option autoImplicit false

namespace PathRecording.Supplement

open Matrix MeasureTheory

universe u v

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 1.3, p.9 (with footnote 9 and its proof in §4.2.2, pp.51–52): given
black-box access to `Q^{Tab}_ρ`, the tableau oracles `Q^{Tab}_{ρ⊤}`, `Q^{Tab}_{ρ*}`, `Q^{Tab}_{ρ†}`
are each implemented by a single application of `Q^{Tab}_ρ` (or of its complex conjugate
`\overline{Q^{Tab}_ρ}`, for conjugate and transpose queries) with simple pre- and post-processing.
Precisely: for every map `T` on `V ⊗ Tab(Ĝ)` with `Q_ρ (I ⊗ F⁻¹) = (I ⊗ F⁻¹) T` on square-summable
inputs (so `T = Q^{Tab}_ρ`), and every square-summable input,
1. `Q_{ρ⊤} (I ⊗ F⁻¹) = (I ⊗ F⁻¹) (I ⊗ Sw) \overline{T} (I ⊗ Sw)`;
2. `Q_{ρ*} (I ⊗ F⁻¹) = (I ⊗ F⁻¹) (I ⊗ D_J) \overline{T} (I ⊗ \overline{D_J})`;
3. `Q_{ρ†} (I ⊗ F⁻¹) = (I ⊗ F⁻¹) (I ⊗ D_J Sw) T (I ⊗ D_J Sw)`,
where `\overline{T} = K T K`, `Sw : |λ,X,Y⟩ ↦ |λ,Y,X⟩`, and `D_J` is the relabelling between an irrep
and its dual. The pre- and post-processing depend only on `Ĝ` and `J`, not on `ρ` or `T`.

**Formalization Note.**
* `V ⊗ Tab(Ĝ)` is `Fin N → (TabIdx Ĝ → ℂ)`; an input is square-summable when every component is
  (`Memℓp · 2`). `I ⊗ F⁻¹` is `fourierInv μ Ĝ` componentwise; `Q_ρ` is the published `oracle`, and
  `Q_{ρ⊤}, Q_{ρ*}, Q_{ρ†}` are `matOracle` of `ρ(g)⊤`, `\overline{ρ(g)}`, `ρ(g)†` in the basis `B(V)`.
* `T` is an arbitrary map, required to preserve square-summability and to satisfy the intertwining
  on square-summable inputs; this determines `T` there, since `F⁻¹` is injective (Lemma 3.8).
* `μ` is a regular left Haar probability measure (Definition 3.1: "regular Borel"), so inversion
  preserves it. -/
theorem theorem_1_3 {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] [μ.Regular] (Ĝ : GHat.{u, v} G) (D : DualData Ĝ) {N : ℕ}
    (ρ : UnitaryRep G N) (T : (Fin N → Ĝ.TabIdx → ℂ) → (Fin N → Ĝ.TabIdx → ℂ))
    (hT : ∀ w : Fin N → Ĝ.TabIdx → ℂ, (∀ x, Memℓp (w x) 2) →
      (∀ x, Memℓp (T w x) 2) ∧
        PathRecording.oracle μ ρ (fun x => fourierInv μ Ĝ (w x)) =
          fun x => fourierInv μ Ĝ (T w x))
    (w : Fin N → Ĝ.TabIdx → ℂ) (hw : ∀ x, Memℓp (w x) 2) :
    matOracle μ (transposeMap ρ) (fun x => fourierInv μ Ĝ (w x)) =
        (fun x => fourierInv μ Ĝ
          (swapTab (conjTab (T (fun x' => conjTab (swapTab (w x'))) x)))) ∧
    matOracle μ (conjMap ρ) (fun x => fourierInv μ Ĝ (w x)) =
        (fun x => fourierInv μ Ĝ
          (dualMap D (conjTab (T (fun x' => conjTab (conjDualMap D (w x'))) x)))) ∧
    matOracle μ (adjMap ρ) (fun x => fourierInv μ Ĝ (w x)) =
        (fun x => fourierInv μ Ĝ
          (dualMap D (swapTab (T (fun x' => dualMap D (swapTab (w x'))) x)))) := by sorry

end PathRecording.Supplement
