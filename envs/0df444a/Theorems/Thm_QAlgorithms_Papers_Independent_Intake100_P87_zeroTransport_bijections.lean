-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P87_zeroTransport_bijections
-- name    : QAlgorithms.Papers.Independent.Intake100.P87.zeroTransport_bijections
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:29:56.760438+00:00
-- url     : https://prove2.me/theorems/ef82f01d-adb4-454a-a06d-a4148f29e063
-- title:
--   Smooth degree-zero transport is smooth G-valued functions
-- statement:
--   Let $M,Y,G$ be ordinary finite-dimensional real smooth manifolds, let $\pi:Y\to M$ be any smooth surjective submersion, and let $i:G\to T$ be an injective map into a set $T$. A smooth degree-zero descent datum is a smooth map $\mathrm{triv}:Y\to G$ whose image under $i$ is constant on every fibre of $\pi$. A transport $0$-functor with $G$-structure is a map $F:M\to T$ admitting a smooth local $G$-valued lift along some smooth surjective submersion.
--
--   Both specified comparison maps are bijections:
--
--   $$
--   r_\pi:C^\infty(M,G)\longrightarrow\operatorname{Des}^0_\pi(i)^\infty,
--   \quad f\longmapsto f\circ\pi,
--   $$
--   $$
--   c_i:C^\infty(M,G)\longrightarrow\operatorname{Trans}^0_G(M,T),
--   \quad f\longmapsto i\circ f.
--   $$
--
--   Thus smooth descent and degree-zero transport recover the unique global smooth $G$-valued function through the actual local-descent maps. No contractibility, global smooth section, group structure on $G$, smooth structure on $T$, or surjectivity of $i$ is required.
-- source:
--   Parallel Transport and Functors, arXiv:0705.0452v5, PDF p. 48, zero-transport

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P87

noncomputable section

open scoped ContDiff Manifold

namespace QAlgorithms.Papers.Independent.Intake100.P87

universe u v

/-- Smooth degree-zero transport identification, Section 7.1, PDF pp. 48–49.
Both specified comparison maps are bijections, for every smooth surjective submersion;
i is injective, G need not be a group, and T is merely a set. -/
theorem zeroTransport_bijections {Y M G : SmoothManifold.{u}} {T : Type v}
    (pi : SmoothSurjectiveSubmersion Y M) (i : G.carrier → T)
    (hi : Function.Injective i) :
    Function.Bijective (zeroSmoothPullback pi i) ∧
    Function.Bijective (zeroTransportOfSmooth (M := M) i) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P87

end
