-- Prove2me | Theorems.Thm_SymCircMM_theorem_3_3_frobenius_reciprocity
-- name    : SymCircMM.theorem_3_3_frobenius_reciprocity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:30:55.006534+00:00
-- url     : https://prove2.me/theorems/227ab0de-5095-434e-bb70-709763fcf397
-- title:
--   Theorem 3.3 — Frobenius reciprocity over any field, with the explicit inverse $\psi\mapsto\Phi_\psi$
-- statement:
--   Let $H\le G$, let $W$ be a representation of $H$ and $U$ a representation of $G$, both over a field $F$, and let $\mathrm{Ind}_H^GW=\bigoplus_rt_r\otimes W$ be built from a left transversal $t_1=1,t_2,\dots,t_m$ as in display (3), with $\iota(w)=1\otimes w$. Then the map
--
--   $$\mathrm{Hom}_G\bigl(\mathrm{Ind}_H^GW,U\bigr)\longrightarrow\mathrm{Hom}_H\bigl(W,\mathrm{Res}_HU\bigr),\qquad \Phi\longmapsto\Phi\circ\iota,$$
--
--   is an isomorphism of $F$-vector spaces, with inverse $\psi\mapsto\Phi_\psi$, where $\Phi_\psi(t_r\otimes w)=t_r\cdot\psi(w)$.
--
--   The paper states reciprocity in this explicit form because most sources assume $F=\mathbb C$; it feeds Proposition 3.4.
--
--   **Formalization Note** The conclusion is a linear equivalence $e$ between the spaces of intertwining maps with $e(\Phi)=\Phi\circ\iota$ and $e^{-1}(\psi)(t_r\otimes w)=t_r\cdot\psi(w)$; in particular $\Phi_\psi$ is $G$-equivariant.
--
--   Differences from the source:
--
--   - generalization: H ≤ G finite groups and finite-dimensional representations W, U → G any group, H a subgroup of finite index, W and U any F-modules; reason: the paper's setting is an instance; the statement and the construction need only a finite transversal
--   - encoding: Ind^G_H W = ⨁_r t_r ⊗ W with the action (3), and the map ι → indRep H T ρW on functions G ⧸ H → W, t_r ⊗ w = Pi.single r w, and indIota; reason: for finite index the function space is the direct sum, and the action is (3)
--   - encoding: Hom_G(Ind W, U) → Hom_H(W, Res_H U), Φ ↦ Φ ∘ ι, an isomorphism with inverse ψ ↦ Φ_ψ → ∃ e : IntertwiningMap (indRep H T ρW) ρU ≃ₗ[F] IntertwiningMap ρW (ρU.comp H.subtype) with e Φ = Φ ∘ ι and e.symm ψ (Pi.single r w) = ρU (t_r) (ψ w); reason: the same claim; Φ_ψ is determined by its values on the t_r ⊗ w
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Theorem 3.3, p.9 (PDF p.10); proof Appendix B, pp.17–18 (PDF pp.18–19)

import Mathlib
import Definitions.Def_SymCircMM_indRep

open scoped Classical

set_option autoImplicit false

namespace SymCircMM

/-- **Theorem 3.3** (Frobenius reciprocity; Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.9 (PDF p.10); proof Appendix B, pp.17–18
(PDF pp.18–19)): "Let H ≤ G, let W be a representation of H and U a representation of G, both over some
field F. Then the map Hom_G(Ind^G_H W, U) → Hom_H(W, Res_H U), Φ ↦ Φ ∘ ι is an isomorphism of
F-vector spaces, with inverse ψ ↦ Φ_ψ, where Φ_ψ(t_r ⊗ w) := t_r · ψ(w)."

**Formalization Note.** `Ind^G_H W` is `indRep T ρW` for a left transversal `T` with `t₁ = 1`, on
functions `G ⧸ H → W` (`t_r ⊗ w = Pi.single r w`), and `ι = indIota`. `Hom_G` and `Hom_H` are the
spaces of intertwining maps. The conclusion is a linear equivalence `e` with `e Φ = Φ ∘ ι` whose inverse
sends `ψ` to the intertwining map with `Φ_ψ(t_r ⊗ w) = t_r · ψ(w)`. `H` has finite index, and `G`, `W`,
`U` are otherwise arbitrary. -/
theorem theorem_3_3_frobenius_reciprocity {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (T : LeftTransversal H) {F W U : Type} [Field F] [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U] (ρW : Representation F H W) (ρU : Representation F G U) :
    ∃ e : Representation.IntertwiningMap (indRep H T ρW) ρU ≃ₗ[F]
        Representation.IntertwiningMap ρW (ρU.comp H.subtype),
      (∀ Φ, (e Φ).toLinearMap = Φ.toLinearMap ∘ₗ indIota H) ∧
      (∀ ψ (q : G ⧸ H) (w : W), e.symm ψ (Pi.single q w) = ρU (T.t q) (ψ w)) := by sorry

end SymCircMM
