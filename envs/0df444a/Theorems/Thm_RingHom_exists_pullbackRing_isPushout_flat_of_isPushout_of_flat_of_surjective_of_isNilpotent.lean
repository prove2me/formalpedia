-- Prove2me | Theorems.Thm_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
-- name    : RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/f2a151ce-5a5a-5479-adc8-3f2bf522dd03
-- title:
--   Flat patching along a fibre product of nilpotent thickenings
-- statement:
--   Let $B$, $B'$, $B''$ be commutative rings and let $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ be ring homomorphisms that are surjective and whose kernels are nilpotent ideals. Write $P$ for `pullbackRing` $\varphi'\,\varphi''$, the subring of $B' \times B''$ on which $\varphi' \circ \mathrm{pr}_1$ and $\varphi'' \circ \mathrm{pr}_2$ agree, with the two projections `pullbackFst`, `pullbackSnd` to $B'$ and $B''$. Let further $A'$, $A''$, $A_0$ be commutative rings with ring maps $a' : B' \to A'$, $a'' : B'' \to A''$, $a_0 : B \to A_0$, $g' : A' \to A_0$, $g'' : A'' \to A_0$ such that, in `CommRingCat`, the square formed by $\varphi'$, $a'$, $a_0$, $g'$ is a pushout and likewise the square formed by $\varphi''$, $a''$, $a_0$, $g''$, and assume $a'$ and $a''$ are flat. Then there is a ring homomorphism $a$ from $P$ to `pullbackRing` $g'\,g''$ (the subring of $A' \times A''$ on which $g' \circ \mathrm{pr}_1$ and $g'' \circ \mathrm{pr}_2$ agree) such that: $a$ followed by each projection of `pullbackRing` $g'\,g''$ equals the corresponding projection of $P$ followed by $a'$, respectively $a''$; the square formed by the two projections of `pullbackRing` $g'\,g''$ together with $g'$ and $g''$ is a pullback in `CommRingCat`; $g''$ is surjective and every element of its kernel is nilpotent; the square formed by `pullbackFst` $\varphi'\,\varphi''$, $a$, $a'$ and `pullbackFst` $g'\,g''$ is a pushout, and likewise with the second projections; $a$ is flat; and if $a'$ and $a''$ are of finite presentation, so is $a$.
--
--   This is the affine form of Milnor-style patching in its flat version: flat algebras over the two sides of a fibre product of rings along surjections with nilpotent kernel glue to a flat algebra over the fibre product, with the given algebras recovered as base changes. It is used by [`AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing`](thm.html#AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing), the scheme-level statement built from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
    (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
    (H' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom a') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g'))
    (H'' : IsPushout (CommRingCat.ofHom φ'') (CommRingCat.ofHom a'') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g''))
    (hfl' : a'.Flat) (hfl'' : a''.Flat) :
    ∃ a : pullbackRing φ' φ'' →+* pullbackRing g' g'',
      (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ'') ∧
      (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'') ∧

      IsPullback (CommRingCat.ofHom (pullbackFst g' g'')) (CommRingCat.ofHom (pullbackSnd g' g''))
        (CommRingCat.ofHom g') (CommRingCat.ofHom g'') ∧
      Function.Surjective g'' ∧ (∀ x ∈ RingHom.ker g'', IsNilpotent x) ∧

      IsPushout (CommRingCat.ofHom (pullbackFst φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a')
        (CommRingCat.ofHom (pullbackFst g' g'')) ∧
      IsPushout (CommRingCat.ofHom (pullbackSnd φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a'')
        (CommRingCat.ofHom (pullbackSnd g' g'')) ∧

      a.Flat ∧ (a'.FinitePresentation → a''.FinitePresentation → a.FinitePresentation) := by sorry
