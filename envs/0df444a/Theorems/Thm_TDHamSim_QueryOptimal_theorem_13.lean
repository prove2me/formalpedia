-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_theorem_13
-- name    : TDHamSim.QueryOptimal.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:44.83473+00:00
-- url     : https://prove2.me/theorems/f46a9cb2-fe2d-4481-99a5-65cca2d5c02d
-- title:
--   Theorem 13 — query-optimal and gate-efficient simulation
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every $n,a$, $\alpha>0$, $\beta\ge0$, $T>0$ and $0<\varepsilon\le1/2$. If $\alpha T\le\varepsilon$, the identity circuit with no gates, queries or auxiliary wires simulates every admissible Hamiltonian. Otherwise there are a natural number $q$, a power of two $J=2^m$ (the HAM-T grid), a number $k$ of auxiliary wires, and a fixed standard oracle circuit, chosen before $H$ and its blocks, such that
--
--   $$q\le C\left(\alpha T+\frac{\log(1/\varepsilon)}{\log(e+\log(1/\varepsilon)/(\alpha T))}\right),\qquad\#\mathrm{queries}=12q,$$
--   $$k\le C\left(a+\log\left(1+\frac{T(\alpha+\beta T)}{\varepsilon}\right)\right),$$
--   $$\#\mathrm{additional\ gates}\le Cq\left(a+\log\left(1+\frac{T(\alpha+\beta T)}{\varepsilon}\right)\right).$$
--
--   For every Hermitian $H$ satisfying (7), every Hermitian unitary HAM-T block family satisfying (9) at the chosen grid, and every unit $\psi$, its full output error is
--
--   $$\|U_{\rm sim}(|0\rangle\otimes\psi)-|0\rangle\otimes U_H(T)\psi\|\le\varepsilon.$$
--
--   The gate and auxiliary bounds do not grow with $n$. Auxiliary wires are retained in the output comparison.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: O(·) resource bounds → one positive absolute real constant chosen before all parameters; reason: a single constant can dominate the finitely many universal constants, with logarithm-base factors absorbed
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Theorem 13 — query-optimal and gate-efficient simulation, p.33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Theorem 13, p.33: both branches and all three resource bounds, with a circuit
chosen before H and its oracle blocks and an absolute constant chosen before every parameter. -/
theorem theorem_13 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n a : ℕ) (α β T ε : ℝ),
      0 < α → 0 ≤ β → 0 < T → 0 < ε → ε ≤ 1/2 →
      (α*T ≤ ε → ∀ H : ℝ → Mat (Bits n), IsHamiltonian H α β T →
        Simulates ([] : ConstDepthUnitary.OCircuit (Wires n 0) 0) 1 (propagator H T T) ε) ∧
      (ε < α*T → ∃ m q k : ℕ,
        ∃ c : ConstDepthUnitary.OCircuit (Wires n k) (1+m+a+n),
          c.IsStandard ∧ c.queries = 12*q ∧
          (q : ℝ) ≤ C*qStar α T ε ∧ (k : ℝ) ≤ C*nStar a α β T ε ∧
          (extraGates c : ℝ) ≤ C*q*nStar a α β T ε ∧
          ∀ (H : ℝ → Mat (Bits n)) (O : Fin (2^m) → Mat (Bits a × Bits n)),
            IsHamiltonian H α β T → IsHAMT H α T O →
            Simulates c (controlledHAMT O) (propagator H T T) ε) := by sorry

end TDHamSim.QueryOptimal
