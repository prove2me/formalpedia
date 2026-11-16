-- Prove2me | Theorems.Thm_PathRecording_Supplement_theorem_4_1
-- name    : PathRecording.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:32:40.847998+00:00
-- url     : https://prove2.me/theorems/d9d56480-6662-4fc3-995f-11d1c4e382da
-- title:
--   Theorem 4.1 — in the Fourier basis, $Q_\rho$ is the Clebsch–Gordan / inverse dual Clebsch–Gordan update
-- statement:
--   Let $G$ be a compact group with its normalized Haar measure, $\widehat G$ the complete catalogue of its irreducible representations, and $(C,dC)$ a Clebsch–Gordan transform and a dual Clebsch–Gordan transform that are compatible in the sense of (3.13). Let $\rho=\bigoplus_\mu I_{M_\mu}\otimes\rho_\mu$ be a finite-dimensional unitary representation in block-diagonal form, with basis $|\mu,m,x\rangle$ of $V$. Then for every basis vector $|\mu,m,x\rangle\otimes|\lambda,X,Y\rangle$ of $V\otimes\mathrm{Tab}(\widehat G)$,
--   $$Q_\rho\big(|\mu,m,x\rangle\otimes F^{-1}|\lambda,X,Y\rangle\big)=\sum_{y,\lambda^+,r,X^+,Y^+}\langle\lambda^+,\mu,Y^+,y|\,dC^\dagger\,|\lambda^+,\mu,\lambda,r,Y\rangle\,\langle\lambda,\mu,\lambda^+,r,X^+|\,C\,|\lambda,\mu,X,x\rangle\;|\mu,m,y\rangle\otimes F^{-1}|\lambda^+,X^+,Y^+\rangle .$$
--   Equivalently, $(I\otimes F)\,Q_\rho\,(I\otimes F)^{-1}$ is the tableau recording update: apply $C$ to $|\lambda,\mu,X,x\rangle$, then $dC^\dagger$ to the registers $(\lambda^+,\mu,\lambda,r,Y)$, return $|\mu,m,y\rangle$ and keep $|\lambda^+,X^+,Y^+\rangle$.
--
--   So the uncompressed representation oracle is isometric to the tableau recording oracle via the Fourier transform, an explicit Uhlmann transformation between the two; the tableau oracle is efficient whenever the Clebsch–Gordan transforms are.
--
--   **Formalization Note** The sum runs over a finite set of labels $\lambda^+$ containing all those with $m^{\lambda^+}_{\lambda,\mu}\neq0$. Lemma 3.21 asserts that compatible pairs exist; it is not part of this mission, so the hypothesis is not known in Lean to be satisfiable.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized bi-invariant Haar measure of Definition 3.1
--   - encoding: V ⊗ L²(G) with Q_M(|x⟩⊗|f⟩) = ∫ f(g) M(g)|x⟩⊗|g⟩ dg → functions from the basis of V to Lp ℂ 2 μ, with (Q_M φ)_y = Σ_x M(·)_{yx} · φ_x (matrix entries as L^∞ multipliers); reason: Eq. (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^{dim V}
--   - encoding: (I⊗F)·Q_ρ·(I⊗F)⁻¹ equals the tableau update U_{C,dC} on V ⊗ ⨁_λ V_λ ⊗ V_λ* → Q_ρ(|µ,m,x⟩ ⊗ F⁻¹|λ,X,Y⟩) = Σ_{y,λ⁺,r,X⁺,Y⁺} (update coefficient) |µ,m,y⟩ ⊗ F⁻¹|λ⁺,X⁺,Y⁺⟩ for every basis vector; reason: F is unitary (Theorem 3.6) and both sides are bounded linear, so the identity on the basis vectors, which span a dense subspace, is the operator identity; U_{C,dC} is the bounded extension of the right side
--   - reading: the theorem's text names no condition on C and dC → C and dC compatible in the sense of (3.13); reason: footnote 44 ('Technically, we need compatible Clebsch–Gordan and dual Clebsch–Gordan transforms') and the proof's use of the dagger of Lemma 3.21 at (4.19)
--   - encoding: ρ in an irreducible decomposition V ≃ ⨁_µ M_µ ⊗ V^µ_G with basis |µ⟩⊗|m⟩⊗|x⟩ (4.3) → a finite family of catalogue labels µ_i with ρ = ⨁_i ρ_{µ_i} on V = ⨁_i V^{µ_i}_G, basis ⟨i, x⟩; reason: repeated labels are the multiplicity space M_µ; this is the basis the paper works in (p.48, footnote 43)
--   - encoding: Ĝ the set of isomorphism classes of irreps; Tab(Ĝ) with basis |λ,X,Y⟩ and F⁻¹|λ,X,Y⟩ = √d_λ ∫⟨Y|ρ_λ(g)|X⟩|g⟩dg → a complete catalogue of pairwise inequivalent continuous irreducible unitary representations, with F⁻¹|λ,X,Y⟩ the normalized matrix coefficient in L²(μ); reason: Definition 3.7; Peter–Weyl's F itself is not formalized
--   - encoding: dC_{λ⁺,µ} with multiplicity spaces M^λ_{λ⁺,µ,*} and (3.13) using the same index r as C → the multiplicity of λ in λ⁺⊗µ* is indexed by the same Fin m^{λ⁺}_{λ,µ} as in C; reason: the two multiplicities are equal (Frobenius reciprocity), and (3.13) identifies the index sets
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 4.1, p.49; tableau update §4.2, p.48, Eqs. (4.19)–(4.21), pp.50–51; footnote 44, p.48

import Mathlib
import Definitions.Def_PathRecording_Supplement_matOracle
import Definitions.Def_PathRecording_Supplement_CGPair

set_option autoImplicit false

namespace PathRecording.Supplement

open Matrix MeasureTheory

universe u v

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 4.1 (Clebsch–Gordan Updates for Tableau Recordings), p.49, with the
update rule of §4.2 (p.48, Eqs. (4.19)–(4.21), pp.50–51): in the Fourier basis, the uncompressed
representation oracle is the tableau recording update "Clebsch–Gordan transform followed by an
inverse dual Clebsch–Gordan transform". For every complete irrep catalogue `Ĝ`, every compatible
pair `(C, dC)` (Eq. (3.13)), every block-diagonal `ρ = ⨁_i ρ_{µ_i}` (Eq. (4.3)) and every basis
vector `|µ, m, x⟩ ⊗ |λ, X, Y⟩`,
`Q_ρ(|µ, m, x⟩ ⊗ F⁻¹|λ, X, Y⟩) = Σ_{y, λ⁺, r, X⁺, Y⁺} ⟨λ⁺, µ, Y⁺, y| dC† |λ⁺, µ, λ, r, Y⟩ ⟨λ, µ, λ⁺, r, X⁺| C |λ, µ, X, x⟩ · |µ, m, y⟩ ⊗ F⁻¹|λ⁺, X⁺, Y⁺⟩`,
i.e. `Q_ρ (I ⊗ F⁻¹) = (I ⊗ F⁻¹) U_{C,dC}`, equivalently `(I ⊗ F) Q_ρ (I ⊗ F)⁻¹ = U_{C,dC}`.

**Formalization Note.**
* `V = ⨁_i V^{µ_i}_G` has basis `⟨i, x⟩`; the component `i` plays the role of `|µ, m⟩` with
  `µ = µ_i` (repeated labels are the multiplicity space `M_µ`). `Q_ρ = matOracle μ (blockRep Ĝ lab)`,
  which is `Σ_µ |µ⟩⟨µ| ⊗ I_{M_µ} ⊗ Q_{ρ_µ}` (4.3).
* The identity is stated on every basis vector of `V ⊗ Tab(Ĝ)`, with `F⁻¹|λ, X, Y⟩ = coeffFn μ Ĝ ⟨λ,(X,Y)⟩`.
  Both sides are bounded linear maps, so this is the operator identity on all of `V ⊗ Tab(Ĝ)`; the
  update `U_{C,dC}` is the bounded extension of the right-hand side. All labels `λ ∈ Ĝ` are
  allowed, not only those reachable after `t` queries.
* The sum runs over `λ⁺ ∈ supp λ µ`; labels outside it have multiplicity `0`. -/
theorem theorem_4_1 {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (Ĝ : GHat.{u, v} G) (P : CGPair Ĝ) (hP : P.Compatible)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (lab : κ → Ĝ.Charge)
    (i : κ) (x : Fin (Ĝ.dim (lab i))) (b : Ĝ.TabIdx) :
    matOracle μ (blockRep Ĝ lab) (Pi.single ⟨i, x⟩ (coeffFn μ Ĝ b)) =
      ∑ y : Fin (Ĝ.dim (lab i)), ∑ bp : P.supp b.1 (lab i), ∑ r : Fin (P.mult b.1 (lab i) bp),
        ∑ Xp : Fin (Ĝ.dim bp), ∑ Yp : Fin (Ĝ.dim bp),
          P.updateCoeff b.1 (lab i) b.2.1 b.2.2 x y bp r Xp Yp •
            Pi.single (⟨i, y⟩ : Σ j, Fin (Ĝ.dim (lab j))) (coeffFn μ Ĝ ⟨bp.1, (Xp, Yp)⟩) := by sorry

end PathRecording.Supplement
