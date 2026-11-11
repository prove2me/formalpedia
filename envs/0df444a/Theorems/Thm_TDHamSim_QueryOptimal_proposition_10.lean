-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_proposition_10
-- name    : TDHamSim.QueryOptimal.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:15.39746+00:00
-- url     : https://prove2.me/theorems/00cb943c-701b-4ed7-b6d8-30224b227555
-- title:
--   Proposition 10 — controlled implementation
-- statement:
--   There is an absolute constant $C>0$ such that, for every number of system and oracle-ancilla qubits, every $J=2^m\ge2$, and every $0<w\le1$, each of controlled $S^\circ$ and controlled $(S^\circ)^\dagger$ has a standard query-free implementation with
--
--   $$\text{additional gates}\le C(a+m+1),\qquad\text{work qubits}\le C(a+m+1).$$
--
--   The implementation is exact on every input vector when its work wires start in zero, and those wires return exactly to zero. The circuit count is independent of the number of system qubits.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: O(·) resource bounds → one positive absolute real constant chosen before all parameters; reason: a single constant can dominate the finitely many universal constants, with logarithm-base factors absorbed
--   - generalization: the section regime with q≥max{1,αT} and J≥max{2,q} → all J≥2 and every 0<w≤1, including arbitrary system-register size; reason: only w and the register dimensions enter the controlled update operator
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Proposition 10 — controlled implementation, p.28. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Proposition 10, p.28: universal constants and exact clean-workspace implementations. -/
theorem proposition_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a n : ℕ) (w : ℝ), 1 ≤ m → 0 < w → w ≤ 1 →
      ∀ dagger : Bool, ∃ k : ℕ,
      ∃ c : ConstDepthUnitary.OCircuit (Wires (1+(1+m+a+n)) k) 0,
        c.IsStandard ∧ c.queries = 0 ∧ (k : ℝ) ≤ C*(a+m+1) ∧
        (extraGates c : ℝ) ≤ C*(a+m+1) ∧
        Implements c 1 (ctrl (if dagger then (physical m a n (updates (2^m) a n w)).conjTranspose
          else physical m a n (updates (2^m) a n w))) := by sorry

end TDHamSim.QueryOptimal
