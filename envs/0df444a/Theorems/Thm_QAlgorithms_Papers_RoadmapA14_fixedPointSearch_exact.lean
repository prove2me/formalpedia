-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA14_fixedPointSearch_exact
-- name    : QAlgorithms.Papers.RoadmapA14.fixedPointSearch_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:37.803363+00:00
-- url     : https://prove2.me/theorems/f99666a5-b38e-4c88-be9d-e6126492d179
-- title:
--   Fixed-point quantum search: exact Chebyshev success profile and L−1 queries
-- statement:
--   Let $n,l\ge 0$ be integers, $L=2l+1$, and $\delta\in[0,1]$. Let $A$ be a unitary on $n$ qubits, $|s\rangle=A|0\rangle^{\otimes n}$, and let $|T\rangle$ be a unit vector with $\lambda=|\langle T|s\rangle|^2>0$. The supplied target oracle is
--   $$
--   U=I+|T\rangle\langle T|\otimes(X-I),
--   $$
--   where $X$ flips the additional qubit: $U$ flips it on $|T\rangle$ and acts identically on the orthogonal complement.
--
--   Define $\gamma=1/\cosh(\operatorname{arcosh}(1/\delta)/L)$ for $\delta>0$, and $\gamma=0$ for $\delta=0$. For $j=1,\ldots,l$, set
--   $$
--   \alpha_j=2\left(\frac{\pi}{2}-\arctan\!\left(\tan(2\pi j/L)\sqrt{1-\gamma^2}\right)\right),
--   \qquad \beta_j=-\alpha_{l-j+1}.
--   $$
--   With $S_s(\alpha)=I-(1-e^{-i\alpha})|s\rangle\langle s|$, $S_T(\beta)=I-(1-e^{i\beta})|T\rangle\langle T|$, and $G(\alpha,\beta)=-S_s(\alpha)S_T(\beta)$, define $S_L=G(\alpha_l,\beta_l)\cdots G(\alpha_1,\beta_1)$; the empty product is $I$.
--
--   There is an absolute constant $C>0$ such that, for each $n,l,\delta$, a single circuit template chosen before $A,T,U$ implements $S_L$ up to a global phase on every data vector, returning its one ancillary qubit to $|0\rangle$. It uses exactly $2l=L-1$ plain $U$ queries and $2l$ total calls to $A$ or $A^\dagger$, no controlled oracle calls, and at most $Cl(n+1)^2$ elementary gates from arbitrary single-qubit unitaries and CNOT. Preparation of the supplied input $|s\rangle$ is outside these counts. Oracle calls are charged separately from elementary gates.
--
--   Writing $T_L$ for the Chebyshev polynomial of the first kind, both the constructed sequence and this physical circuit have target success probability
--   $$
--   P_L(\lambda,\delta)=|\langle T|S_L|s\rangle|^2
--   =\begin{cases}
--   1-\delta^2 T_L\!\left(\sqrt{1-\lambda}/\gamma\right)^2,&\delta>0,\\
--   1-(1-\lambda)^L,&\delta=0.
--   \end{cases}
--   $$
--   In particular,
--   $$
--   \lambda\ge w_L(\delta):=1-\gamma^2
--   \quad\Longrightarrow\quad P_L(\lambda,\delta)\ge 1-\delta^2.
--   $$
--
--   The guaranteed interval gives fixed-point amplitude amplification with an adjustable failure tolerance and exactly $L-1$ target-oracle queries. The endpoints $l=0$, $\lambda=1$, $n=0$, and $\delta=0,1$ are included.
--
--   **Formalization Note** The joint overlap with $|T\rangle|0\rangle$ is the physical success probability because the ancillary qubit is returned clean. The endpoint $\delta=0$ uses the continuous limiting polynomial confirmed on PDF p.4, rather than division by zero.
-- source:
--   Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, Equation (1); PDF p.2 uniform bound; p.3 Eqs. (10)–(11), Fig.2, PDF p. 1. https://arxiv.org/abs/1409.3305v2 . PDF SHA-256: 82e0a88496d56ab79338abb202e99b678210ed367d6e7c99ab719a8c87055c50.

import Definitions.Def_QAlgorithms_Defs_FixedPointSearch
import Definitions.Def_QAlgorithms_Defs_CircuitResources
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapA14

/-- Yoder, Low, Chuang, arXiv:1409.3305v2, PDF p.1 Eq. (1), p.2 guaranteed
interval, and p.3 Eqs. (10)--(11) and Fig.2. For every odd length `L = 2*l+1`
and tolerance `delta` in `[0,1]`, one input-independent circuit implements the
explicit phase sequence up to global phase, with `L-1` plain target-flip queries,
one reusable clean ancilla, and an absolute quadratic elementary-gate overhead.
The success identity and uniform error bound include the continuous endpoint
`delta = 0` (p.4); neither the identity nor sequence unitarity is assumed.
The target projector avoids the inconsistent rephasing of Eq. (4) on p.2.
-/
theorem fixedPointSearch_exact :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n l : ℕ) (delta : ℝ), 0 ≤ delta → delta ≤ 1 →
        ∃ c : OracleCircuit singleQubitCnotGateSet ![n, n + 1] (n + 1),
          c.queryCount 1 = 2 * l ∧ c.controlledQueryCount 1 = 0 ∧
          c.queryCount 0 = 2 * l ∧ c.controlledQueryCount 0 = 0 ∧
          (c.gateCount : ℝ) ≤ C * (l : ℝ) * ((n : ℝ) + 1) ^ 2 ∧
          ∀ (A : Matrix (Qubits n) (Qubits n) ℂ)
            (T : EuclideanSpace ℂ (Qubits n))
            (U : Matrix (Qubits n × Bool) (Qubits n × Bool) ℂ),
            A ∈ Matrix.unitaryGroup (Qubits n) ℂ → IsTargetFlipOracle T U →
            inner ℂ T (act A (zeroKet n)) ≠ 0 →
            let s := act A (zeroKet n)
            let lam := ‖inner ℂ T s‖ ^ 2
            let O : (k : Fin 2) → Matrix (Qubits (![n, n + 1] k))
                (Qubits (![n, n + 1] k)) ℂ :=
              Fin.cases A (Fin.cases (U.submatrix
                (fun z : Qubits (n + 1) => (Fin.init z, z (Fin.last n)))
                (fun z : Qubits (n + 1) => (Fin.init z, z (Fin.last n))))
                (fun k : Fin 0 => Fin.elim0 k))
            let phi := act (c.unitary O) (zeroAncillaVec s 1)
            (∃ theta : ℝ, ImplementsWithCleanAncillas (c.unitary O)
              (Complex.exp (Complex.I * (theta : ℂ)) • fixedPointSequence l delta A T)) ∧
            ‖inner ℂ T (act (fixedPointSequence l delta A T) s)‖ ^ 2 =
              fixedPointProfile l lam delta ∧
            ‖inner ℂ (zeroAncillaVec T 1) phi‖ ^ 2 = fixedPointProfile l lam delta ∧
            (fixedPointWidth l delta ≤ lam →
              1 - delta ^ 2 ≤ ‖inner ℂ (zeroAncillaVec T 1) phi‖ ^ 2) := by sorry

end QAlgorithms.Papers.RoadmapA14
