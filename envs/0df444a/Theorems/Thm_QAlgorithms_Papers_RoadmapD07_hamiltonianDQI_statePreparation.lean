-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapD07_hamiltonianDQI_statePreparation
-- name    : QAlgorithms.Papers.RoadmapD07.hamiltonianDQI_statePreparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:44:36.53972+00:00
-- url     : https://prove2.me/theorems/1f61cd41-1cf9-4eda-b77e-176730e4ac05
-- title:
--   Hamiltonian DQI: exact polynomial-state preparation with one decoder call
-- statement:
--   Let $n,m\ge 1$ and $\ell\ge 0$ be integers. Let $H=\sum_{i=1}^{m}c_iP_i$ be a classically known Hamiltonian on $n$ qubits, where $c_i\in\mathbb R$ and the $P_i$ are distinct canonical Hermitian Pauli operators that commute pairwise. Let $P(x)=\sum_{j=0}^{\ell}a_jx^j$ be a real polynomial of degree exactly $\ell$, and assume $P(H)\ne 0$. Write $B^\top\in\mathbb F_2^{2n\times m}$ for the matrix whose columns are the symplectic labels of the $P_i$, with the $Z$ coordinates preceding the $X$ coordinates. Assume there exists a unitary decoder $D$ on the $m$-qubit label register and the $2n$-qubit syndrome register satisfying
--   $$
--   D|y\rangle|B^\top y\rangle=|0\rangle|B^\top y\rangle\quad(1\le |y|\le\ell),
--   \qquad w_0\ne0\ \Longrightarrow\ D|0\rangle|0\rangle=|0\rangle|0\rangle.
--   $$
--   Here $|y|$ is Hamming weight and $w_0$ is the zero-string reference coefficient defined below. The zero-branch guarantee is required only when $w_0\ne0$; when $w_0=0$, that decoder input is unrestricted. All other decoder inputs are unrestricted.
--
--   There is an exact quantum preparation circuit, chosen from the known Hamiltonian and polynomial before choosing the decoder, that works for every decoder with these guarantees and prepares
--   $$
--   \rho_P(H)=\frac{P(H)^2}{\operatorname{Tr}[P(H)^2]}.
--   $$
--   It starts with zeroed registers, uses exactly one plain forward application of $D$, and uses no adjoint or controlled decoder calls. The output is the reduced density matrix after discarding the other registers, with no postselection or success-probability qualification.
--
--   For clarity, define the real reference coefficients and their normalization by
--   $$
--   w_y=\sum_{j=0}^{\ell}a_jj!
--   \sum_{\substack{\mu\in\mathbb Z_{\ge0}^{m}\\|\mu|=j,\ \mu\equiv y\pmod2}}
--   \frac{\prod_{i=1}^{m}c_i^{\mu_i}}{\prod_{i=1}^{m}\mu_i!},
--   \qquad
--   \mathcal N=\sqrt{\sum_{y\in\{0,1\}^{m}}w_y^2}.
--   $$
--   The reference $|R\rangle=\mathcal N^{-1}\sum_yw_y|y\rangle$ is constructed by the algorithm, rather than supplied as input. In particular,
--   $$
--   \mathcal N>0,\qquad
--   \mathcal N^2=\frac{\operatorname{Tr}[P(H)^2]}{2^n},\qquad
--   |\phi\rangle=\mathcal N^{-1}(P(H)\otimes I)|\Phi_n\rangle,\qquad
--   \operatorname{Tr}_{C}|\phi\rangle\langle\phi|=\rho_P(H),
--   $$
--   where $|\Phi_n\rangle=2^{-n/2}\sum_z|z\rangle_B|z\rangle_C$; both $|R\rangle$ and $|\phi\rangle$ have unit norm.
--
--   The circuit includes a concrete classical arithmetic program that computes $\mathcal N$ and all boundary and local-matrix entries of the reference MPS from the coefficients alone. It may introduce only the numeric constants $0,1,-1$, and the entries of its quantum gates are obtained from that program's results. There exist an absolute $C>0$, a polynomial $q$ with nonnegative integer coefficients, and thresholds $\ell_0\ge1$ and $s_0$, all independent of sizes, Pauli terms, coefficients, and decoder, such that
--   $$
--   T_{\rm classical}\le C m\ell^3\quad(\ell\ge\ell_0),\qquad
--   T_{\rm quantum}\le C m q(\ell+n)\quad(\ell+n\ge s_0).
--   $$
--   Here classical cost counts actual arithmetic and memory instructions, and quantum cost counts the circuit's gate and oracle steps plus initialization of its qubits. This is the paper's ideal model with unit-cost real arithmetic and exact arbitrary one- and two-qubit unitary gates.
--
--   This result supplies an exact polynomial-filtered density matrix using a perfect decoder even for general real commuting Pauli coefficients, without assuming the reference state has already been prepared.
--
--   **Formalization Note.** The proof's $j=0,\ldots,\ell$ convention replaces the theorem display's $j=1,\ldots,\ell$. Real polynomial coefficients, the nonzero condition, and the decoder's zero-branch guarantee for an occupied reference branch are explicit corrections needed for normalization and coherence. The conditional zero-branch guarantee strengthens literal Eq. (7) only when $w_0\ne0$ and is not inferred from it. Pauli-product phases are retained through the Bell basis change and its inverse. The ordinary positive-$n,m$ regime is explicit; nonzero constant polynomials are included, and asymptotic bounds are applied only above their stated thresholds.
--
--   **Correction to the printed source.**
--
--   Printed: Theorem 5 displays j=1,...,l, does not explicitly type a_j or exclude P(H)=0, and refers to Eq.(7), which specifies decoder action only for 1<=|y|<=l. The proof suppresses Pauli-product phases in its Bell-basis display.
--
--   Corrected: Use the proof convention j=0,...,l with real polynomial coefficients; require P(H)!=0; retain Eq.(7) and require D|0,0>=|0,0> only if the Eq.(10) coefficient w_0 is nonzero. Preserve product phases under the coherent Bell transform and its inverse.
--
--   Reason: The proof and MPS boundaries include a_0. Real coefficients and P(H)!=0 make P(H)^2/Tr[P(H)^2] a density matrix. Eq.(7) leaves an occupied zero branch uncontrolled; fixing only that occupied branch restores coherent erasure without excluding H=I,P=x, whose w_0 vanishes and whose positive-weight decoder necessarily moves |0,0>. A linear Bell transform must preserve Pauli-product signs.
-- source:
--   Hamiltonian Decoded Quantum Interferometry for General Pauli Hamiltonians, arXiv:2601.18773v1, Theorem 5, §3 (proof continues on PDF p.9), PDF p. 8. https://arxiv.org/abs/2601.18773v1 . PDF SHA-256: a363ba68a1ecc190cd7dd5c0c744a5e1fc00034e823a11a55df2ca80a707cea0.

import Definitions.Def_QAlgorithms_Defs_HDQIPreparation
import Definitions.Def_QAlgorithms_Papers_RoadmapD07_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.RoadmapD07




/-- Theorem 5 (arXiv:2601.18773v1, PDF pp.8-9), with the proof's necessary
corrections: real coefficients and the `j = 0,...,l` convention of Eqs.(10),(20);
`P(H) != 0` so Eq.(19) defines a density matrix; and decoder fixation of `|0,0>`
when its reference coefficient is nonzero, in addition to the positive-weight
action in Eq.(7). This is an additional guarantee, not a consequence of Eq.(7).
When that coefficient vanishes, no zero-branch action is imposed; in particular,
the identity-Pauli instance `H = I`, `P(x) = x` remains admissible.

The ordinary nonempty regime has `n,m >= 1`; degree zero is allowed. The
absolute constants, polynomial, and asymptotic thresholds precede every size
and coefficient. The concrete preparation, including its counted classical
computation, precedes every admissible decoder. The ideal model uses exact
one- and two-qubit gates and unit-cost real arithmetic/memory operations.

The reference normalization and normalized purification are conclusions, not
assumed resources. Pauli products retain their phases under the coherent Bell
basis change and its inverse (the proof's phase-suppressed display on p.9 is
read linearly). Preparation is exact, with no postselection. -/
theorem hamiltonianDQI_statePreparation :
    ∃ C : ℝ, 0 < C ∧ ∃ q : Polynomial ℕ, ∃ l0 : ℕ, 1 ≤ l0 ∧ ∃ s0 : ℕ,
      ∀ (n m l : ℕ), 1 ≤ n → 1 ≤ m →
      ∀ (labels : Fin m → CanonicalPauliLabel n) (c : Fin m → ℝ) (P : Polynomial ℝ),
        Function.Injective labels →
        (∀ i j, (canonicalPauli (labels i)).Commute (canonicalPauli (labels j))) →
        P.natDegree = l →
        Polynomial.aeval (pauliHamiltonian labels c) P ≠ 0 →
        (∃ D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ,
          IsWeightDecoder labels l D ∧
            (parityMultinomialCoefficient c P l 0 ≠ 0 →
              act D (ket (0, 0)) = ket (0, 0))) →
        let H := pauliHamiltonian labels c
        let M : Matrix (Qubits n) (Qubits n) ℂ := Polynomial.aeval H P
        let N := hdqiReferenceNorm c P l
        let phi := ((N⁻¹ : ℝ) : ℂ) •
          act (Matrix.kronecker M (1 : Matrix (Qubits n) (Qubits n) ℂ)) (maxEntangled n)
        0 < N ∧ N ^ 2 = (M ^ 2).trace.re / (2 : ℝ) ^ n ∧
          0 < (M ^ 2).trace.re ∧ IsState (hdqiReference c P l) ∧
          IsState phi ∧ traceRight (pureDensity phi) = polynomialDensity H P ∧
          ∃ prep : HDQIPreparation n m,
            prep.classicalInput = coefficientInput c P l ∧
            HasStandardConstants prep.preprocessing ∧
            (∃ result, prep.preprocessing.eval prep.classicalInput = some result ∧
              ComputesReferenceData c P l result) ∧
            (l0 ≤ l → (prep.classicalCost : ℝ) ≤ C * m * (l : ℝ) ^ 3) ∧
            (s0 ≤ l + n →
              ((prep.circuit.length + m + (n + n) + prep.work : ℕ) : ℝ) ≤
                C * m * ((q.eval (l + n) : ℕ) : ℝ)) ∧
            prep.circuit.plainQueryCount 0 = 1 ∧
            prep.circuit.controlledQueryCount 0 = 0 ∧
            (∀ (k : Fin 1) (adj : Bool) (ctl : Option (Fin (m + (n + n) + prep.work)))
              (wires : Fin ((fun _ : Fin 1 => m + (n + n)) k) ↪
                Fin (m + (n + n) + prep.work))
              (hc : ∀ a, ctl = some a → a ∉ Set.range wires),
              OracleStep.query k adj ctl wires hc ∈ prep.circuit → adj = false ∧ ctl = none) ∧
            ∀ D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ,
              IsWeightDecoder labels l D →
                (parityMultinomialCoefficient c P l 0 ≠ 0 →
                  act D (ket (0, 0)) = ket (0, 0)) →
                prep.output D = polynomialDensity H P := by sorry

end QAlgorithms.Papers.RoadmapD07
