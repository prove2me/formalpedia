-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA05_matrixQSVT_synthesis
-- name    : QAlgorithms.Papers.RoadmapA05.matrixQSVT_synthesis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:41:32.585566+00:00
-- url     : https://prove2.me/theorems/76073417-6768-4f4c-8693-dd16ebf41f57
-- title:
--   U(N)-QSVT: coherent synthesis of a contracting complex polynomial matrix
-- statement:
--   Let $d\geq 0$ be an integer and let $P=(P_{kj})$ be an $r\times c$ matrix of complex polynomials, with $r,c\geq 1$. Each entry has degree at most $d$ and parity $d$: $P_{kj}(-x)=(-1)^dP_{kj}(x)$. Suppose
--
--   $$
--   I_c-P(x)^\dagger P(x)\succeq 0\qquad\text{for every }x\in[-1,1].
--   $$
--
--   Let $\mathcal I,\mathcal O,\mathcal K$ be positive finite input, output, and signal registers, and fix known isometric computational-basis embeddings $\iota:\mathcal I\hookrightarrow\mathcal K$ and $\omega:\mathcal O\hookrightarrow\mathcal K$. The mixing register has $q$ qubits, with fixed embeddings of the $c$ input labels and $r$ output labels in its $2^q$ basis states; unused rows and columns are zero padded. An admissible oracle is any unitary $U$ on $\mathcal K$ with exact unscaled block $A=U[\omega,\iota]:\mathcal I\to\mathcal O$.
--
--   There are $d+1$ known unitary mixers on the mixing register enlarged by one flag qubit, and a fixed identification of the flag and mixing registers, chosen from $P,d$ and the known embeddings before $U$ or $A$ is supplied. The resulting synthesis circuit alternates these known operations with exactly $d$ uncontrolled oracle calls $U,U^\dagger,U,U^\dagger,\ldots$. A mixer acts conditioned on the known input signal projector at even stages and the known output signal projector at odd stages. For every admissible oracle and every family of input vectors $\phi_j\in\mathcal I$, the entire flag-zero component of its output is
--
--   $$
--   |0\rangle_{\mathrm{flag}}\sum_{k=1}^{r}|k\rangle_{\mathrm{mix}}\,\iota_d\!\left(\sum_{j=1}^{c}P_{kj}^{(\mathrm{SV})}(A)\phi_j\right).
--   $$
--
--   Here the input is $|0\rangle_{\mathrm{flag}}\sum_{j=1}^{c}|j\rangle_{\mathrm{mix}}\,\iota(\phi_j)$, and $\iota_d=\iota$ for even $d$ and $\iota_d=\omega$ for odd $d$. Writing $P_{kj}(x)=\sum_a p_{kj,a}x^a$, the singular-value transforms are
--
--   $$
--   P_{kj}^{(\mathrm{SV})}(A)=
--   \begin{cases}
--   \displaystyle\sum_{a=0}^{\lfloor d/2\rfloor}p_{kj,2a}(A^\dagger A)^a,&d\text{ even},\\[4pt]
--   \displaystyle\sum_{a=0}^{\lfloor d/2\rfloor}p_{kj,2a+1}A(A^\dagger A)^a,&d\text{ odd}.
--   \end{cases}
--   $$
--
--   All remaining amplitude lies in flag one. This simultaneously block-encodes the whole polynomial matrix at normalization one and error zero, without a positive success-probability guarantee. The formula includes the input kernel in the even case, where the constant coefficient acts as a multiple of the identity. Singular $A$, rectangular $A$ and $P$, zero $P$, and $d=0$ are permitted. A normalized joint input gives a physical state, while the equality itself is linear and holds for all vectors.
--
--   This theorem supplies coherent matrix-valued singular-value synthesis under a single matrix contraction condition. No Hermiticity, invertibility, determinant constraint, finite gate set, or classical synthesis-time estimate is imposed.
--
--   **Formalization Note** The printed Theorem 10 omits the degree and common-parity requirements used by its proof; these are explicit here. The output signal zero register and the orientation of the singular-vector decomposition are corrected according to Eqs. (1) and (31)–(35). The printed claim and these corrections are recorded separately in the audit notes. Known embeddings express the all-zero signal-ancilla subspaces in register-independent coordinates.
-- source:
--   Quantum Signal Processing and Quantum Singular Value Transformation on $U(N)$, arXiv:2408.01439v4, Theorem 10 (U(N)-QSVT, backward), §2.3, Eq. (38), pp. 7–8, PDF p. 7. https://arxiv.org/abs/2408.01439v4 . PDF SHA-256: 9eaee44d32cdbbd7c45dcc646b5829b3943ad8de6fc5781ed939846e1ee04529.

import Definitions.Def_QAlgorithms_Defs_MatrixQSVTCircuits
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.RoadmapA05

open QAlgorithms.MatrixQSVT

/-- Lu, Liu and Lin, arXiv:2408.01439v4, Theorem 10, PDF pp. 7-8,
Eq. (38), with proof through p. 9: simultaneous complex matrix singular-value
transformation by an oracle-independent synthesis with exactly `d` alternating,
uncontrolled calls to `U` and its adjoint.

`PolynomialData` makes explicit the entrywise degree bound and common parity
used by Theorem 2 and Lemmas 8 and 11, but omitted from the printed Theorem 10.
The output uses the input signal space for even `d` and the output signal space
for odd `d`, correcting the repeated output `|0>` in Eq. (38) and the reversed
singular-vector labels in Eq. (2), consistently with Eqs. (1), (31)-(35).
The projector order follows these equations rather than the reversed labels
in the Fig. 3 caption: input at even stages, output at odd stages.
The contraction hypothesis is the printed matrix positivity condition; no
polynomial completion is assumed. Rectangular polynomial blocks are padded via
known row and column embeddings in `P`. All flag-zero coordinates, including
those outside the selected output embedding, are fixed by `IsFlaggedRealization`.
The equality holds on every input vector and has normalization one and error zero.
Degree zero, zero-qubit mixing registers, zero polynomials, and singular blocks
are allowed. No gate-count, classical synthesis-time, or success-probability
lower bound is claimed. -/
theorem matrixQSVT_synthesis
    {r c d : ℕ} (P : PolynomialData r c d)
    (hcontract : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ((1 : Matrix (Fin c) (Fin c) ℂ) - (P.eval x)ᴴ * P.eval x).PosSemidef)
    (I O K : Type) [Fintype I] [Fintype O] [Fintype K]
    [Nonempty I] [Nonempty O] [Nonempty K]
    [DecidableEq I] [DecidableEq O] [DecidableEq K]
    (input : I ↪ K) (output : O ↪ K) :
    ∃ S : SynthesisData I O K (P.mixingQubits + 1) d,
      S.input = input ∧ S.output = output ∧
      ∃ mixingLayout : Qubits (P.mixingQubits + 1) ≃ Bool × Qubits P.mixingQubits,
        S.circuit.queryCount 0 = d ∧
        ∀ (U : Matrix K K ℂ) (A : Matrix O I ℂ),
          IsRectangularEncoding input output U A →
          IsFlaggedRealization P S mixingLayout U A := by sorry

end QAlgorithms.Papers.RoadmapA05
