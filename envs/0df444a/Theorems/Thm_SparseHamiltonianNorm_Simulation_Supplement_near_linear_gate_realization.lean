-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_Supplement_near_linear_gate_realization
-- name    : SparseHamiltonianNorm.Simulation.Supplement.near_linear_gate_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:31:46.740225+00:00
-- url     : https://prove2.me/theorems/b023317b-68d4-4d54-aebd-3e32efdee8a0
-- title:
--   Theorem 3 — Near-linear gate realization
-- statement:
--   There exist absolute positive constants $C_q,C_0$ such that, for every choice of polynomial arithmetic-library constants $c_A,k_A$, there are a positive constant $C$ and a natural exponent $k$, independent of every problem instance, with the following property. Let $1\le d\le N$, $t\ge0$, $0<\Lambda_{\max}\le\Lambda$, and $0<\varepsilon\le1/2$, with the four numerical parameters rational. Retain the published sparse-access promises and precision predicate. Sufficient value precision exists, and the conclusion holds at every sufficient precision $(p',k')$.
--
--   Let $b_{\rm val}$ bound the value-register width and all four public parameter lengths, define $Q_{\rm sim}$ as in Eq. (14), and put $X=\lceil\log_2 N\rceil+b_{\rm val}+\log d+\log(2Q_{\rm sim}/\varepsilon)$. If the arithmetic library is available through length $\lceil C_0(1+X)\rceil$ with reusable workspace $a_{\rm ar}$, one finite sparse-oracle circuit $c$ with $w$ work qubits exists such that
--   $$Q(c)\le C_q Q_{\rm sim},$$
--   $$G(c)+g_F Q_F(c)+g_H Q_H(c)\le C Q_{\rm sim}\bigl(g_F+g_H+(1+X)^k\bigr),$$
--   $$w+\lceil\log_2 N\rceil+a_F+a_H\le C_q(X+a_F+a_H+a_{\rm ar}).$$
--   Here $G(c)$ counts ordinary one- and two-qubit gates, while $Q_F,Q_H$ count all calls to the respective oracle, including inverse and controlled calls. The last two bounds hold for every supplied oracle gate and workspace cost. The same circuit, chosen before the hidden matrix, row permutations and value table, has full clean-output operator-norm error at most $\varepsilon$ for every compatible complex Hermitian input. Every output ancilla is covered, and $N=1,d=1,t=0$ remain included.
--
--   This companion theorem adds gate and space costs to the live mission's query bound. It assumes neither qRAM nor free access to clock-amplitude tables. Its supporting continuous-to-finite comparison is Lemma 16.
--
--   Differences from the source:
--   - reading: public numerical parameters of bounded bit length and fixed-precision arithmetic → rational parameters with reduced numerator/denominator lengths and explicitly sized signed fixed-point calls on valid representable outputs; reason: the finite-register assumption needs a format, range and overflow convention; binary points and every register bit are charged, and no Hamiltonian is restricted
--   - generalization: uniform reversible arithmetic circuits with polynomial size → reversible arithmetic libraries without a uniformity requirement and with the same size and clean-workspace bounds; reason: every source uniform library satisfies the predicate; the conclusion requires no uniform circuit-generation algorithm
--   - encoding: supplied controlled/inverse oracle circuits costing gF,gH and using aF,aH workspaces → one oracle-generic circuit charged gF and gH per query and aF+aH extra qubits for all four costs; reason: query counters include inverse and controlled calls; substituting supplied oracle circuits yields the literal resource bounds
--   - encoding: O(Qsim), poly(X), and O(X+aF+aH+aar), with Eq. (138) working precision → absolute constants Cq (queries, qubits) and C0 (library length ceil(C0(1+X))) chosen first, then for each cA,kA a gate constant C and exponent k, all before instances; reason: this spells out the asymptotic constants as the proof on pp.34–35 supplies them; only poly(·) depends on the arithmetic library
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Theorem 3, p.4 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Supplement_Arithmetic

namespace SparseHamiltonianNorm.Simulation.Supplement
open QAlgorithms
/-- Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026),
Theorem 3, p.4, Eqs. (14)--(16), with working precision Eq. (138), p.35.
The query/qubit constant Cq and the working-length constant C0 are absolute
(pp.34--35); only the gate constant C and the degree k of poly(·) depend on the
arithmetic library's polynomial (cA, kA). All constants precede the instance. One circuit, fixed before the hidden input,
carries the query, gate, qubit and full clean-output error conclusions. -/
theorem near_linear_gate_realization :
    ∃ Cq C0 : ℝ, 0 < Cq ∧ 0 < C0 ∧
    ∀ cA kA : ℕ, ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
    ∀ (N d : ℕ) (t Λ Λmax ε : ℚ),
      1 ≤ d → d ≤ N → 0 ≤ t → 0 < Λ → 0 < Λmax → Λmax ≤ Λ →
      0 < ε → ε ≤ 1 / 2 →
      ∃ p kv : ℕ, SufficientPrecision d t Λ Λmax ε p kv ∧
      ∀ p' k' : ℕ, SufficientPrecision d t Λ Λmax ε p' k' →
      ∀ bval : ℕ, ParametersFit bval k' t Λ Λmax ε →
      ∀ aar : ℕ,
        ArithmeticLibrary cA kA
          ⌈C0 * (1 + resourceArgument N d bval t Λ Λmax ε)⌉₊ aar →
      ∃ (w : ℕ) (c : SparseCircuit N k' (w + addressBits N)),
        (sparseQueries c : ℝ) ≤ Cq * simulationScale d t Λ Λmax ε ∧
        (∀ gF gH aF aH : ℕ,
          ((c.gateCountWhere (fun _ => True) +
              gF * c.queryCount 0 + gH * c.queryCount 1 : ℕ) : ℝ) ≤
            C * simulationScale d t Λ Λmax ε *
              (gF + gH + (1 + resourceArgument N d bval t Λ Λmax ε) ^ k) ∧
          ((w + addressBits N + aF + aH : ℕ) : ℝ) ≤
            Cq * (resourceArgument N d bval t Λ Λmax ε + aF + aH + aar)) ∧
        ∀ (H : Matrix (Fin N) (Fin N) ℂ) (f : Fin N → Equiv.Perm (Fin N))
          (table : Fin N → Fin N → Qubits (valueBits k')),
          SparsePromise d Λ Λmax H → ListsSupport d H f → ValueTableFor p' k' H table →
          CleanSimulation w t ε H (c.unitary (sparseOracles f table)) := by sorry
end SparseHamiltonianNorm.Simulation.Supplement
