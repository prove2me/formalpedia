-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P87_zeroDescent_bijection
-- name    : QAlgorithms.Papers.Independent.Intake100.P87.zeroDescent_bijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:29:17.627065+00:00
-- url     : https://prove2.me/theorems/5f12e25d-8387-4436-ab77-99a1197d071e
-- title:
--   Degree-zero extraction is a bijection
-- statement:
--   Let $M,Y,G$ be ordinary finite-dimensional real smooth manifolds, let $\pi:Y\to M$ be a smooth surjective submersion, let $T$ be a set, and let $i:G\to T$ be injective. Neither a group structure on $G$ nor a smooth structure on $T$ is assumed. Let $\operatorname{Triv}^0_\pi(i)$ consist of pairs $(F,\mathrm{triv})$ with $F:M\to T$, $\mathrm{triv}:Y\to G$, and $F\circ\pi=i\circ\mathrm{triv}$. Let $\operatorname{Des}^0_\pi(i)$ consist of functions $\mathrm{triv}:Y\to G$ such that $i(\mathrm{triv}(y))=i(\mathrm{triv}(z))$ whenever $\pi(y)=\pi(z)$.
--
--   The specified extraction map is a bijection, and every descent function has a unique $G$-valued factor:
--
--   $$
--   \operatorname{Ex}_\pi:(F,\mathrm{triv})\longmapsto\mathrm{triv}
--   \quad\text{is bijective},\qquad
--   \forall\mathrm{triv}\in\operatorname{Des}^0_\pi(i),\quad
--   \exists! f:M\to G\;\;f\circ\pi=\mathrm{triv}.
--   $$
--
--   This is set-valued descent along the actual cover, with no smoothness requirement on the descent function.
-- source:
--   Parallel Transport and Functors, arXiv:0705.0452v5, PDF p. 48, zero-descent

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P87

noncomputable section

open scoped ContDiff Manifold

namespace QAlgorithms.Papers.Independent.Intake100.P87

universe u v

/-- Degree-zero descent, Section 7.1, PDF pp. 48–49: Ex_pi is a bijection;
each descent function has a unique factor through pi with values in G. -/
theorem zeroDescent_bijection {Y M G : SmoothManifold.{u}} {T : Type v}
    (pi : SmoothSurjectiveSubmersion Y M) (i : G.carrier → T)
    (hi : Function.Injective i) :
    Function.Bijective (zeroExtract pi i) ∧
    ∀ data : ZeroDescent pi i, ∃! f : M.carrier → G.carrier,
      ∀ y, f (pi.toFun y) = data.val y := by sorry

end QAlgorithms.Papers.Independent.Intake100.P87

end
