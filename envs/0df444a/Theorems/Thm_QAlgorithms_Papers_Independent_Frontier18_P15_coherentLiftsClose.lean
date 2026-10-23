-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P15_coherentLiftsClose
-- name    : QAlgorithms.Papers.Independent.Frontier18.P15.coherentLiftsClose
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:05:47.405211+00:00
-- url     : https://prove2.me/theorems/b6b421e2-3ad3-41b0-8b13-86e01213ff65
-- title:
--   Coherent lifts of nearby probability laws
-- statement:
--   Let $\{|x\rangle\}_{x=1}^d$ be an orthonormal basis of a nonzero finite quantum system and let $p,q$ be probability distributions on its labels. Define the normalized vectors $|\psi\rangle=\sum_x\sqrt{p_x}|x\rangle$ and $|\phi\rangle=\sum_x\sqrt{q_x}|x\rangle$. For every $\epsilon\ge0$, if the corresponding diagonal density operators are within $\epsilon$ in full trace norm, then
--
--   $$
--   \left\||\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|\right\|_1\le2\sqrt{\epsilon}.
--   $$
--
--   This controls the distance between the pure states coherently representing the two laws. The columns of an arbitrary unitary specify the orthonormal basis; the norm in the conclusion is a projector trace norm, rather than a vector norm.
-- source:
--   A Resource Framework for Quantum Shannon Theory, arXiv:quant-ph/0512015v1, PDF p. 9, Corollary 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P15

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P15

/-- Corollary 2.3, PDF p.9. The columns of U are the arbitrary orthonormal basis.
The conclusion compares pure-state projectors with the full trace norm. -/
theorem coherentLiftsClose (d : ℕ) (hd : 0 < d)
    (p q : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpSum : ∑ i, p i = 1) (hqSum : ∑ i, q i = 1)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hclose : traceNorm
      (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.diagonal fun i => (p i : ℂ)) -
       conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.diagonal fun i => (q i : ℂ))) ≤
      epsilon) :
    traceNorm
      (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift p)) -
       pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift q))) ≤
      2 * Real.sqrt epsilon := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P15

end
