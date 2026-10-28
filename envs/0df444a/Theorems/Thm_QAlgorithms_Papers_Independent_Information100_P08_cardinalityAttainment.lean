-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_cardinalityAttainment
-- name    : QAlgorithms.Papers.Independent.Information100.P08.cardinalityAttainment
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:57:36.911069+00:00
-- url     : https://prove2.me/theorems/85465070-09de-4feb-af3b-8366b9d49b38
-- title:
--   Proposition 2.1: cardinality and attainment
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. There is a finite ensemble $e$, with at most $d_A^2$ members, such that $$F_{\mathcal N}(e)=U_F(\mathcal N).$$ This gives both attainment and the cardinality bound; zero weights may pad an ensemble.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 12, Proposition 2.1: cardinality and attainment

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Proposition 2.1: the supremum is attained, with at most d_A^2 mixed members. -/
theorem cardinalityAttainment {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N) :
    ∃ e : Ensemble (Fin a), e.size ≤ a ^ 2 ∧ channelObjective N e = channelPotential N := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
