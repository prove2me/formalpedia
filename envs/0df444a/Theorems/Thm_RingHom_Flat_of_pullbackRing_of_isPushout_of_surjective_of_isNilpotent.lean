-- Prove2me | Theorems.Thm_RingHom_Flat_of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
-- name    : RingHom.Flat.of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/c62a4075-d2cf-5b16-8ac8-8bbe52ff857e
-- title:
--   Flatness over a fibre product along nilpotent thickenings
-- statement:
--   Let $B$, $B'$, $B''$ be commutative rings and let $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ be surjective ring homomorphisms whose kernels are nilpotent ideals (some power of each kernel is the zero ideal). Let $A'$, $A''$, $A_0$ be commutative rings and let $a' : B' \to A'$, $a'' : B'' \to A''$, $a_0 : B \to A_0$, $g' : A' \to A_0$, $g'' : A'' \to A_0$ be ring homomorphisms such that the square formed by $\varphi'$, $a'$, $a_0$, $g'$ and the square formed by $\varphi''$, $a''$, $a_0$, $g''$ are both pushout squares in the category of commutative rings (so $A_0$ is $A' \otimes_{B'} B$ and also $A'' \otimes_{B''} B$), and assume $a'$ and $a''$ are flat, i.e. $A'$ is flat over $B'$ and $A''$ is flat over $B''$. Here `pullbackRing` of two maps with common target denotes the subring of the product consisting of pairs with equal images, with `pullbackFst` and `pullbackSnd` its two coordinate projections. Finally let $a : B' \times_B B'' \to A' \times_{A_0} A''$ be a ring homomorphism whose composites with the two projections of the target equal $a'$, respectively $a''$, composed with the corresponding projections of the source. Then $a$ is flat, that is, $A' \times_{A_0} A''$ is flat as a module over $B' \times_B B''$ via $a$.
--
--   This is the glueing statement for flatness over a fibre product of rings along two surjections with nilpotent kernel, the homological ingredient in the construction of pushouts of thickenings. It is cited by [`RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent`](thm.html#RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent), which produces the glued flat algebra over the fibre product together with the two cocartesian squares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_Flat_of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem RingHom.Flat.of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
    (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
    (H' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom a') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g'))
    (H'' : IsPushout (CommRingCat.ofHom φ'') (CommRingCat.ofHom a'') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g''))
    (hfl' : a'.Flat) (hfl'' : a''.Flat)
    (a : pullbackRing φ' φ'' →+* pullbackRing g' g'')
    (ha' : (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ''))
    (ha'' : (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'')) :
    a.Flat := by sorry
