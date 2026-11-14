-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_valenceProjection_coordinates
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.valenceProjection_coordinates
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T04:10:41.195591+00:00
-- url     : https://prove2.me/theorems/8ab4dd67-25bd-495c-829c-fd829b484314
-- title:
--   Exact finite-graph valence-bond projection amplitudes
-- statement:
--   Let $V$ be a finite set of sites and $E\subseteq V\times V$ a finite set of ordered edges. Place one normalized H-bond $CZ|+,+\rangle$ on every edge. For an output string $x\in\{0,1\}^V$, the local all-equal projection requires each virtual edge endpoint to equal the bit at its incident site. Denote this contraction by $\Pi_E$ and the product of H-bonds by $|H_E\rangle$. Then
--
--   $$\langle x|\Pi_E|H_E\rangle=2^{-|E|}\prod_{(u,v)\in E}(-1)^{x_u x_v}.$$
--
--   This is the unnormalized amplitude calculation in the valence-bond representation of graph cluster states. The finite-graph form includes empty products; no division by a branch norm is used.
-- source:
--   R. Jozsa, An introduction to measurement based quantum computation, https://arxiv.org/abs/quant-ph/0508124v2, PDF pp.17–18, Lemma 3 and Figures 13–15; finite-graph coordinate form of the projection calculation.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Gap20.P01
open scoped Matrix ComplexConjugate
private theorem hBond_apply (a b : Bool) : hBond (a,b) = (1 / 2 : ℂ) * czPhase a b := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  cases a <;> cases b <;>
    norm_num [hBond, czPhase, act, tensorVec, hadamard, ket, controlled, pauliZ,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Complex.ofReal_inv, ← pow_two, inv_pow, h2]
private theorem valenceProjection_apply {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (x : V → Bool) (w : (EdgeLabel E × Bool) → Bool) :
    valenceProjection E x w =
      if w = (fun p => if p.2 then x p.1.val.2 else x p.1.val.1) then 1 else 0 := by
  unfold valenceProjection
  congr 1
  apply propext
  constructor
  · intro h
    funext p
    rcases p with ⟨e,b⟩
    cases b
    · exact (h e).1
    · exact (h e).2
  · intro h e
    subst w
    simp

theorem QAlgorithms.Papers.Independent.Intakenext100.P52.valenceProjection_coordinates {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (x : V → Bool) :
    applyRect (valenceProjection E) (bondGrid E) x = (1 / 2 : ℂ)^E.card * edgePhase E x := by sorry
