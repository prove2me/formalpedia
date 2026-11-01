-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P71_chosenSplitting_reconstruction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P71.chosenSplitting_reconstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:43:01.331251+00:00
-- url     : https://prove2.me/theorems/fef943c0-9f2a-405e-86d2-9cf4e8653fb2
-- title:
--   §4.5.2: reconstruction from a chosen splitting
-- statement:
--   Let $[H_\bullet,E,G_\bullet]$ be a butterfly of right crossed modules of group sheaves over a subcanonical site $S$. Choose a homomorphism of sheaves $s:H_0\to E$ satisfying $\pi s=\mathrm{id}_{H_0}$. There is a unique strict morphism $(f_1,f_0):H_\bullet\to G_\bullet$ such that
--
--   $$
--   f_0=j\circ s,\qquad s(\partial_Hh)=\kappa(h)\iota(f_1(h)).
--   $$
--
--   The map $\theta(y,g)=s(y)\iota(g)$ is an isomorphism of the split diagonal extension with the given diagonal. Its multiplication is
--
--   $$
--   (y_0,g_0)(y_1,g_1)=\bigl(y_0y_1,g_0^{f_0(y_1)}g_1\bigr).
--   $$
--
--   It also intertwines the other butterfly maps: $\pi\theta(y,g)=y$, $j\theta(y,g)=f_0(y)\partial_Gg$, $\theta(1,g)=\iota(g)$, and $\theta(\partial_Hh,f_1(h)^{-1})=\kappa(h)$. This reconstructs the strict morphism and the full split butterfly from its chosen homomorphic splitting.
-- source:
--   Butterflies I: morphisms of 2-group stacks, arXiv:0808.3627v2, PDF p. 35, §4.5.2: reconstruction from a chosen splitting

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P71

namespace QAlgorithms.Papers.Independent.Intakenext100.P71

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C]

variable {J : GrothendieckTopology C}

/-- §4.5.2, arXiv:0808.3627v2, PDF p.35.
A chosen homomorphic section reconstructs a unique strict morphism, and
its canonical coordinates identify the diagonal with the split semidirect
extension, including all four butterfly maps and the multiplication law. -/
theorem chosenSplitting_reconstruction [J.Subcanonical]
    {H G : RightCrossedModule.{u, v, w} J} (E : Butterfly H G) (s : Splitting E) :
    ∃! f : StrictMorphism H G,
      (∀ U y, onSections f.f0 U y = onSections E.j U (onSections s.sectionHom U y)) ∧
      (∀ U h, onSections s.sectionHom U (H.d U h) =
        onSections E.kappa U h * onSections E.iota U (onSections f.f1 U h)) ∧
      (∀ U, Function.Bijective (splitCoordinates s U)) ∧
      (∀ (U : C) (a b : H.zero.sections U × G.one.sections U), splitCoordinates s U
          (a.1 * b.1, G.act U a.2 (onSections f.f0 U b.1) * b.2) =
        splitCoordinates s U a * splitCoordinates s U b) ∧
      (∀ U y g, onSections E.pi U (splitCoordinates s U (y, g)) = y) ∧
      (∀ U y g, onSections E.j U (splitCoordinates s U (y, g)) =
        onSections f.f0 U y * G.d U g) ∧
      (∀ U g, splitCoordinates s U (1, g) = onSections E.iota U g) ∧
      (∀ U h, splitCoordinates s U (H.d U h, (onSections f.f1 U h)⁻¹) =
        onSections E.kappa U h) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P71
