-- Prove2me | Theorems.Thm_RingHom_Flat_quotientMap
-- name    : RingHom.Flat.quotientMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e85cc453-6851-52ea-a562-39e01b034898
-- title:
--   Flatness descends to quotients by an ideal of the base
-- statement:
--   Let $R$ and $S$ be commutative rings (in `Type`), let $f : R \to S$ be a ring homomorphism, and suppose $f$ is flat, i.e. $S$, regarded as an $R$-module through $f$, is flat. Let $I$ be an ideal of $R$. Since $I$ is contained in the preimage under $f$ of its pushforward $I \cdot S :=$ `I.map f`, the homomorphism $f$ induces a ring homomorphism $R/I \to S/(I\cdot S)$, namely `Ideal.quotientMap (I.map f) f Ideal.le_comap_map`. The assertion is that this induced homomorphism is again flat: $S/(I \cdot S)$ is a flat module over $R/I$ for the module structure coming from the induced map.
--
--   This is the standard stability of flatness under the base change $R \to R/I$, in the form needed for the quotient map produced by `Ideal.quotientMap`. It is used in the Čerednik–Drinfeld part of the development, where truncated chart rings are seen to be flat over the corresponding truncation of the base, via [`CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueLevel_of_isSchottky`](thm.html#CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueLevel_of_isSchottky).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_Flat_quotientMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.Flat.quotientMap
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) (I : Ideal R) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by sorry
