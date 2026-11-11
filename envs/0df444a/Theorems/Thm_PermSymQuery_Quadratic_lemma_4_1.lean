-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_lemma_4_1
-- name    : PermSymQuery.Quadratic.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:16.658196+00:00
-- url     : https://prove2.me/theorems/6c392ffa-d347-459b-80a5-788d422113b7
-- title:
--   Lemma 4.1 — controlled preparation and projected overlap
-- statement:
--   Let $A$ be a finite alphabet with any injective binary encoding, and let two string circuits $\mathcal A_1,\mathcal A_2$ have query counts $T_1,T_2\le T$ and a common finite output space after initialized registers have been added. Write $\widetilde a_x,\widetilde b_x$ for their normalized final states. There are a finite ancillary workspace, a circuit with $T$ query slots and a fixed input-independent linear isometry $E$ such that its output on every string is
--   $$E\left(\frac{|0\rangle\widetilde a_x+|1\rangle\widetilde b_x}{\sqrt2}\right).$$
--   Further, for every input-independent orthogonal projector $P$ and Hermitian contraction $M$, there is an algorithm with at most $T$ queries whose signed expectation, on every string, is exactly
--   $$\operatorname{Re}\langle P\widetilde a_x,M P\widetilde b_x\rangle.$$
--   The projector is both self-adjoint and idempotent; $M$ is self-adjoint with operator norm at most one. The second algorithm has its own finite workspace and Boolean output map. Both conclusions preserve the query bound, including $T=0$, and describe genuine measurement expectations without postselection.
--
--   Differences from the source:
--   - encoding: positions [N], encoded bit strings, and signed Boolean outputs → Fin N, Fin b → ZMod 2, and true/false output probabilities; reason: these relabel the positions and binary registers and preserve the signed expectation Pr[1] − Pr[0]
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with a Boolean computational-basis output map and arbitrary finite workspace; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries
--   - reading: after adding initialized registers and identifying the output spaces → two given algorithms on the same workspace and a fixed linear isometry into the prepared circuit space; reason: this expresses the stated identification; any two finite output spaces can be padded to a common one
--   - encoding: at most T oracle applications → exactly T slots in the two constructed algorithms; reason: dummy-address queries pad the circuit without changing its output state or distribution
--   - encoding: a Hermitian contraction on the common projected subspace → a Hermitian contraction on the whole output space sandwiched between P on both states; reason: extending by zero and restricting PMP give the same overlap for every source operator
--   - generalization: the standing choice T ≥ 1 in the §4 preamble → Lemma 4.1 also permits T = 0; reason: zero-query final states are input-independent; their controlled preparation and projected overlap can be realized with input-independent operations alone, and all T ≥ 1 instances are retained
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 4.1, PDF p. 15 (printed p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

/-- Lemma 4.1, PDF p.15 (printed p.13). Both controlled preparation and the
projected-overlap measurement are conclusions. The finite common workspace is the source's
identification after padding; the fixed isometry represents added initialized registers. -/
theorem lemma_4_1 {N b T T₁ T₂ : ℕ} {A W : Type} [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W] (enc : A → Bits b) (henc : Function.Injective enc)
    (alg₁ : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) W T₁)
    (alg₂ : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) W T₂)
    (hT₁ : T₁ ≤ T) (hT₂ : T₂ ≤ T) :
    (∃ (m : ℕ) (C : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) (Fin m) T)
      (E : EuclideanSpace ℂ (Bool × StateIndex N b W) →ₗᵢ[ℂ]
        EuclideanSpace ℂ (StateIndex N b (Fin m))),
      ∀ x : Fin N → A, C.finalState (inputOracle enc x) =
        E (branchState (alg₁.finalState (inputOracle enc x))
          (alg₂.finalState (inputOracle enc x)))) ∧
    ∀ (P M : EuclideanSpace ℂ (StateIndex N b W) →L[ℂ]
      EuclideanSpace ℂ (StateIndex N b W)),
      P.comp P = P → ContinuousLinearMap.adjoint P = P →
      ContinuousLinearMap.adjoint M = M → ‖M‖ ≤ 1 →
      ∃ (m : ℕ) (C : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) (Fin m) T)
        (out : StateIndex N b (Fin m) → Bool),
        ∀ x : Fin N → A, signed enc C out x =
          (inner ℂ (P (alg₁.finalState (inputOracle enc x)))
            (M (P (alg₂.finalState (inputOracle enc x))))).re := by sorry

end PermSymQuery.Quadratic
