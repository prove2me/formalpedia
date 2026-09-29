-- Prove2me | Theorems.Thm_RingHom_bijective_of_surjective_of_smul_eq
-- name    : RingHom.bijective_of_surjective_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e6b0a45c-59ec-56ae-a537-7a6b24c3928f
-- title:
--   Surjections acting on a nontrivial free module are bijective
-- statement:
--   Let $S$ be a commutative ring, $T$ a ring, and $N$ an additive abelian group carrying both an $S$-module structure and a $T$-module structure, with $N$ free as an $S$-module and nontrivial. Let $g \colon S \to T$ be a ring homomorphism, and assume the compatibility $g(s) \cdot n = s \cdot n$ for all $s \in S$ and $n \in N$, that is, the $T$-action on $N$ restricted along $g$ agrees with the given $S$-action. Assume further that $g$ is surjective as a map of sets. The conclusion is that $g$ is bijective. Note that only surjectivity of $g$ is hypothesised and freeness and nontriviality are required of $N$ over $S$ alone; no finiteness or Noetherian hypothesis on $S$ or $N$ is imposed, and no relation between the two module structures beyond the displayed compatibility.
--
--   This is the concluding step of the Taylor–Wiles patching argument in Diamond's formulation: once the patched module is known to be free and nontrivial over the deformation ring, and the deformation ring acts on it through the surjection onto the Hecke algebra, that surjection is an isomorphism. It is used by [`Algebra.PatchingDatum.bijective_and_free_of_surjective`](thm.html#Algebra.PatchingDatum.bijective_and_free_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_bijective_of_surjective_of_smul_eq.lean

import Mathlib.LinearAlgebra.FreeModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RingHom.bijective_of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Function.Bijective g := by sorry
