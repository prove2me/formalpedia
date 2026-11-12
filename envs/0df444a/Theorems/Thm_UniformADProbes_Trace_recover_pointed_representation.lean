-- Prove2me | Theorems.Thm_UniformADProbes_Trace_recover_pointed_representation
-- name    : UniformADProbes.Trace.recover_pointed_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:57.384361+00:00
-- url     : https://prove2.me/theorems/8c4bf9c2-c0a4-4151-a840-1295583fb73d
-- title:
--   Lemma 3.2 — Recovering a pointed representation
-- statement:
--   Consider two real symmetric pairs $(H,K)$ on $\mathbb R^n$ and $(H',K')$ on $\mathbb R^m$, with arbitrary finite ambient dimensions and seeds $v,v'$. Use the same finite polynomial list $U_0,\ldots,U_{M-1}$ with $U_0=1$. Assume its responses span the respective joint cyclic modules. Put $z_i=U_i(H,K)v$ and $z'_i=U_i(H',K')v'$. If the three arrays agree,
--   $$[z_i^Tz_j]=[{z'_i}^Tz'_j],\quad
--   [z_i^THz_j]=[{z'_i}^TH'z'_j],\quad
--   [z_i^TKz_j]=[{z'_i}^TK'z'_j],$$
--   then the two cyclic modules admit a surjective linear isometry that preserves the seed and intertwines both restricted generators.
--
--   The result reconstructs exactly the pointed cyclic representation, permitting different ambient dimensions and zero seeds. The three Gram arrays retain both inner products and generator actions.
--
--   Differences from the source:
--   - generalization: the usual positive matrix orders → also zero ambient dimensions; reason: a zero-dimensional cyclic module and the zero seed satisfy the same Gram and equivalence formulation
--   - encoding: the Gram arrays determine the pointed representation → comparison of two pointed pairs with both spanning hypotheses, equality of all three arrays, and a seed-preserving inner-product-preserving linear equivalence; reason: this is the comparison meaning established in the source proof; explicit action memberships avoid assuming module invariance
--   - encoding: a family U_0, …, U_{M−1} with U_0 = 1 → a list U of integer polynomials with U.head? = some 1; reason: the list is the indexed family; the head condition is U_0 = 1 and forces M ≥ 1
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Lemma 3.2, p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false

namespace UniformADProbes.Trace

theorem recover_pointed_representation (n m : ℕ)
    (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (H' K' : Matrix (Fin m) (Fin m) ℝ) (v' : Fin m → ℝ)
    (hH : H.IsSymm) (hK : K.IsSymm) (hH' : H'.IsSymm) (hK' : K'.IsSymm)
    (U : List NCPoly) (hzero : U.head? = some 1)
    (hspan : responseSpan H K v U = cyclicModule H K v)
    (hspan' : responseSpan H' K' v' U = cyclicModule H' K' v')
    (hgram : gramData H K v U = gramData H' K' v' U) :
    PointedEquivalent H K v H' K' v' := by sorry

end UniformADProbes.Trace
