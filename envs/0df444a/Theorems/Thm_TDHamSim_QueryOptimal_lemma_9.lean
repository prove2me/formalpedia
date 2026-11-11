-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_lemma_9
-- name    : TDHamSim.QueryOptimal.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:14.30759+00:00
-- url     : https://prove2.me/theorems/fee180ee-b667-4955-898c-18b687700421
-- title:
--   Lemma 9 — dyadic factorization
-- statement:
--   Let $J=2^m$ and $0<c<1$. On the ordered public-plus-time space, the independently constructed product $C_J$ and dyadic basis changes satisfy
--
--   $$(\widehat W_J^{\rm out})^\dagger C_J\widehat W_J^{\rm in}=\operatorname{Rot}(c^J)_{\rm pub,0}.$$
--
--   Each lifted basis change fixes the public vector and restricts on the private time basis to $W_J^\star$. The base case $J=1$ is included, as in the source induction. The gates are applied in the source's descending order of time bits.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - generalization: c=(1-w/2)/(1+w/2) in the section regime → every 0<c<1 and every power-of-two J; reason: the dyadic matrix identity holds throughout this interval and includes every source value
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Lemma 9 — dyadic factorization, p.26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Lemma 9, p.26: factorization on the entire stated J+1 dimensional subspace. -/
theorem lemma_9 (m : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    (liftedW m true c).conjTranspose * rotationProduct (2^m) c * liftedW m false c =
      planeRot (2^m) ⟨0, pow_pos (by decide) _⟩ (c^(2^m)) ∧
    (∀ out : Bool, ∀ u : Unit,
      act (liftedW m out c) (WithLp.toLp 2 (fun x => if x = Sum.inl u then 1 else 0)) =
        WithLp.toLp 2 (fun x => if x = Sum.inl u then 1 else 0)) ∧
    (∀ out : Bool, ∀ x y : Fin (2^m), liftedW m out c (Sum.inr x) (Sum.inr y) = timeW m out c x y) := by sorry

end TDHamSim.QueryOptimal
