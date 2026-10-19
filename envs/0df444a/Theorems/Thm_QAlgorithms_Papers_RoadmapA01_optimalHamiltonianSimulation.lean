-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA01_optimalHamiltonianSimulation
-- name    : QAlgorithms.Papers.RoadmapA01.optimalHamiltonianSimulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:21:22.307174+00:00
-- url     : https://prove2.me/theorems/d4d3bcce-7416-426f-b800-00c9de3584cc
-- title:
--   Optimal Hamiltonian simulation by qubitization
-- statement:
--   Let $N,d\ge 1$ be the system and auxiliary dimensions. Let $U$ be a unitary on $\mathbb C^d\otimes\mathbb C^N$, let $G$ be a unitary on $\mathbb C^d$, and write $|g\rangle=G|0\rangle$. Assume that the computed compression $H=(\langle g|\otimes I)U(|g\rangle\otimes I)$ is Hermitian. Access to controlled $U,G$ and their inverses is by black-box queries; arbitrary single- and two-qubit gates are allowed. For real evolution time $t$ and accuracy $0<\varepsilon<1$, define
--   $$
--   Q(t,\varepsilon)=\min\left\{q\in\mathbb Z_{>0}:\frac{4|t|^q}{q!\,2^q}\le\varepsilon\right\}.
--   $$
--   There are positive universal constants $c_{\rm q},C_{\rm q},C_{\rm g},C_{\rm f},C_{\rm s}$ and $\varepsilon_0\in(0,1)$ such that, for every $N,d,t,\varepsilon$, one can choose a circuit independently of the particular $U,G$ that uses at most $\lceil\log_2 N\rceil+\lceil\log_2 d\rceil+2$ qubits. For every such oracle pair with Hermitian compression, its successful system operator $K$, obtained by initializing and postselecting all auxiliary wires to zero, satisfies
--   $$
--   \|K-J_N e^{-iHt}\|_{\rm op}\le\varepsilon,\qquad
--   1-\|K\psi\|_2^2\le C_{\rm f}\varepsilon
--   \quad\text{for every }\psi\in\mathbb C^N\text{ with }\|\psi\|_2=1,
--   $$
--   where $J_N:\mathbb C^N\hookrightarrow(\mathbb C^2)^{\otimes\lceil\log_2 N\rceil}$ is the computational-basis embedding. Thus $K$ includes all possible output amplitudes, even on unused system basis labels. If $T$ is the total number of controlled oracle applications, including inverse applications, and $L_2$ is the number of additional two-qubit gates, the same circuit satisfies
--   $$
--   c_{\rm q}Q(t,\varepsilon)\le T\le C_{\rm q}Q(t,\varepsilon),
--   \qquad L_2\le C_{\rm g}Q(t,\varepsilon)\log d.
--   $$
--   For $0<\varepsilon\le\varepsilon_0$, the factorial scale also satisfies
--   $$
--   Q(t,\varepsilon)\le C_{\rm s}\bigl(|t|+\log(1/\varepsilon)\bigr).
--   $$
--   This is the paper's standard-form simulation procedure and resource guarantee. Its claimed optimality is a worst-case assertion over oracle encodings, supported by the sparse specialization on p.16; the displayed lower query inequality describes the chosen procedure rather than requiring every simulator of each individual Hamiltonian to use that many calls.
--
--   **Formalization Note** Finite-register oracles are extended by the identity on the orthogonal complement of their computational encodings, so neither dimension must be a power of two. The error is the spectral norm of the successful operator itself. The printed $\tau$ in Eq. (1) is undefined in this model; the exact factorial formula fixes $|t|$. The proof's internal accuracy is rescaled to order $\varepsilon^2$ to recover final error $\varepsilon$, and its odd-term sign is reconciled with the headline's $e^{-iHt}$.
-- source:
--   Hamiltonian Simulation by Qubitization, arXiv:1610.06546v3, Theorem 1, Eq. (1), PDF p. 3. https://arxiv.org/abs/1610.06546v3 . PDF SHA-256: 0db700c73663f8034e07316b571dc1b7a6e53f8ad71630db762349fe21d7415c.

import Definitions.Def_QAlgorithms_Defs_Qubitization
import Definitions.Def_QAlgorithms_Defs_CircuitResources
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA01

/-- Low and Chuang, *Hamiltonian Simulation by Qubitization*, arXiv:1610.06546v3,
PDF p.3, Theorem 1 and Eq. (1); standard-form access and gates: pp.4–5;
successful operator block: pp.14–16, Eqs. (29)–(31).

The circuit is chosen before the black-box unitaries. Its total query count is
Theta of the minimal positive factorial-tail scale, and its additional two-qubit
gate count is O(Q log d). All calls are controlled, with adjoints counted once.
Finite-register embeddings extend the oracles by the identity on the complement.
The first ceil(log2 d)+2 wires are postselected to zero; the other wires hold the
encoded system. Error is spectral norm of this successful block, including any
leakage into unused system basis states. Failure is bounded for every unit input.

The printed tau in Eq. (1) is undefined here; its exact factorial expression uses
|t|. The secondary O(|t|+log(1/eps)) estimate is restricted to small error.
The proof's internal tail accuracy must be rescaled to order eps squared to obtain
the stated final error eps. The +i odd part in Eqs. (32),(34) has the wrong sign
for the headline's -i evolution; the target below retains the headline's sign.
The lower query inequality concerns this procedure, not every simulator of each H.
-/
theorem optimalHamiltonianSimulation :
    ∃ CqueryLower CqueryUpper Cgates Cfailure Cscale eps0 : ℝ,
      0 < CqueryLower ∧ 0 < CqueryUpper ∧ 0 < Cgates ∧ 0 < Cfailure ∧
      0 < Cscale ∧ 0 < eps0 ∧ eps0 < 1 ∧
      ∀ (N d : ℕ) [NeZero N] [NeZero d] (t eps : ℝ)
        (heps : 0 < eps), eps < 1 →
        let Q := factorialQueryScale t eps heps
        (eps ≤ eps0 → (Q : ℝ) ≤ Cscale * (|t| + Real.log (1 / eps))) ∧
        ∃ c : OracleCircuit oneTwoQubitGateSet
            (fun k : Fin 2 => if k = 0 then Nat.clog 2 d + Nat.clog 2 N
              else Nat.clog 2 d)
            ((Nat.clog 2 d + 2) + (Nat.clog 2 N + 0)),
          (∀ k : Fin 2, c.plainQueryCount k = 0) ∧
          CqueryLower * (Q : ℝ) ≤ (c.queryCount 0 + c.queryCount 1 : ℕ) ∧
          (c.queryCount 0 + c.queryCount 1 : ℕ) ≤ CqueryUpper * (Q : ℝ) ∧
          (c.gateCountWhere (fun g => g.arity = 2) : ℝ) ≤
            Cgates * (Q : ℝ) * Real.log d ∧
          ∀ (U : Matrix.unitaryGroup (Fin d × Fin N) ℂ)
            (G : Matrix.unitaryGroup (Fin d) ℂ),
            (standardFormSignal (N := N) (d := d) (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ) (G : Matrix (Fin d) (Fin d) ℂ)).IsHermitian →
            let J := (Matrix.kronecker (finiteRegisterEmbedding d)
              (finiteRegisterEmbedding N)).submatrix
                (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 N)) id
            let O : (k : Fin 2) →
                Matrix (Qubits (if k = 0 then Nat.clog 2 d + Nat.clog 2 N
                    else Nat.clog 2 d))
                  (Qubits (if k = 0 then Nat.clog 2 d + Nat.clog 2 N
                    else Nat.clog 2 d)) ℂ :=
              fun k => if h : k = 0 then
                by subst k; exact extendEncodedUnitary J (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ)
              else by
                simpa only [if_neg h] using
                  extendEncodedUnitary (finiteRegisterEmbedding d) (G : Matrix (Fin d) (Fin d) ℂ)
            let V := (c.unitary O).submatrix
              (fun p : Qubits (Nat.clog 2 d + 2) × (Qubits (Nat.clog 2 N) × Qubits 0) =>
                Fin.append p.1 (Fin.append p.2.1 p.2.2))
              (fun p : Qubits (Nat.clog 2 d + 2) × (Qubits (Nat.clog 2 N) × Qubits 0) =>
                Fin.append p.1 (Fin.append p.2.1 p.2.2))
            let K := simulationSuccessOperator (Nat.clog 2 d + 2) 0 V
            specNorm (K - finiteRegisterEmbedding N *
              NormedSpace.exp (-(Complex.I * (t : ℂ)) •
                standardFormSignal (N := N) (d := d) (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ) (G : Matrix (Fin d) (Fin d) ℂ))) ≤ eps ∧
            ∀ psi : EuclideanSpace ℂ (Fin N), IsState psi →
              1 - ‖Matrix.toEuclideanLin K psi‖ ^ 2 ≤ Cfailure * eps := by sorry

end QAlgorithms.Papers.RoadmapA01
