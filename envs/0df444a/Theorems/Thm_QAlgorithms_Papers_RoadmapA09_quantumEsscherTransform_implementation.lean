-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA09_quantumEsscherTransform_implementation
-- name    : QAlgorithms.Papers.RoadmapA09.quantumEsscherTransform_implementation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:37:13.813341+00:00
-- url     : https://prove2.me/theorems/a99e4f02-3e9c-4b7b-a288-c6be8a8cb854
-- title:
--   Quantum Esscher Transform: a subnormalized block-encoding with logarithmic precision dependence
-- statement:
--   Let $d\ge1$, $n,a,n_\rho\ge0$, $\theta\in\mathbb R^d$, and $\kappa>1$ be public parameters. Set
--   $$
--   \beta=\sum_{j=1}^d|\theta_j|+2(1+\log_2(2\kappa)),\qquad
--   L=\log_2(1/\varepsilon),\qquad
--   \varepsilon_{\rm BE}=\left(\frac{\varepsilon}{8L}\right)^2,
--   $$
--   where $0<\varepsilon<2^{-\beta}$. The input $\rho$ is an $n$-qubit trace-one density operator whose eigenvalues lie in $[1/\kappa,1]$. Each $H_j$ is Hermitian with $\|H_j\|_{\rm op}\le1$. Purified access is a unitary $O_\rho$ on $n_\rho+n$ qubits preparing a purification of $\rho$, with the $n_\rho$ ancillary qubits first. Let $U_\rho$ be the exact $(1,n+n_\rho,0)$ block-encoding supplied by the purification construction of Proposition 12. For each $j$, supplied $U_j$ is a $(1,a,\varepsilon_{\rm BE})$ block-encoding of $H_j$; ordinary, adjoint and controlled signal access are available.
--
--   There are universal constants $C_\rho,C_{\rm obs}>0$, a nonnegative integer $p$, and a universal threshold $0<\varepsilon_0<1$ such that, for every admissible public parameter choice with $\varepsilon\le\varepsilon_0$, a QEsscher circuit can be selected before $\rho,H_j,O_\rho,U_j$. This circuit is the logarithm transformation, coefficient state-preparation pair, padded linear combination, and exponential transformation of Algorithm 1. It works for every admissible hidden input and oracle completion. With $b=\lceil\log_2(d+1)\rceil$ and $a_{\rm out}=\max(a,n+n_\rho)+b+4$, its unitary $U_{\rm out}$ satisfies
--   $$
--   \left\|\sigma-(\langle0^{a_{\rm out}}|\otimes I_n)U_{\rm out}(|0^{a_{\rm out}}\rangle\otimes I_n)\right\|_{\rm op}\le\varepsilon,
--   \qquad
--   \sigma=\frac{\exp\!\left(\sum_{j=1}^d\theta_jH_j+\log_2\rho\right)}{4e^\beta}.
--   $$
--   Its oracle counts, including ordinary, adjoint and controlled calls, obey
--   $$
--   q_\rho\le C_\rho\kappa L^2\max\!\left(1,\log_2(2+\kappa L^2)\right)^p,
--   \qquad
--   q_j\le C_{\rm obs}L\quad(j\in[d]).
--   $$
--   The logarithm of a positive matrix is defined by applying $\log_2$ to its eigenvalues; $\exp$ is the natural matrix exponential. The constants, exponent and threshold are independent of all public parameters, hidden matrices and oracle implementations.
--
--   This supplies the subnormalized transform as a block-encoding, useful as an operator primitive. The query count is for $U_\rho$; each such call can be implemented with a constant number of purification-oracle calls. The actual $n_\rho$ is retained in the footprint; the source's $n_\rho=\operatorname{poly}(n)$ is a family convention, and no gate-time conclusion is asserted.
--
--   **Source corrections and limitation.** Algorithm 1 and Step 3 print $b=\lceil\log_2d\rceil$, although their $d+1$ coefficients require $b=\lceil\log_2(d+1)\rceil$. The box prints the divisor $e^\beta$; the statement uses proof Step 5's explicit $4e^\beta$. The printed error schedule is retained. The claim that its numeral 8 ensures Eq. (III.2) has an unresolved quantitative degree-bound gap; accuracy remains the theorem's conclusion, without adding that bound as an assumption.
-- source:
--   The Quantum Esscher Transform, arXiv:2401.07561v2, Theorem 5 (Algorithm 1 and proof, pp.6–7), PDF p. 6. https://arxiv.org/abs/2401.07561v2 . PDF SHA-256: 69a0d58cf4a7248060de63030e90f2a05445a2f75f689e65c967267630bb0117.

import Definitions.Def_QAlgorithms_Defs_EsscherOracleCircuits
import Definitions.Def_QAlgorithms_Papers_RoadmapA09_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA09

open QAlgorithms.QuantumEsscher


/-- Theorem 5, arXiv:2401.07561v2, PDF pp.6–7, Algorithm 1 (called Algorithm III A
in the prose). The public QEsscher construction precedes all hidden inputs and oracle
completions. The target is the absolute operator-norm block-encoding of the subnormalized
transform, and every ordinary, adjoint or controlled oracle call is counted.

Source corrections: the box and Step 3 print `b = ceil(log_2 d)`, despite requiring
`d + 1 <= 2^b`; use `Nat.clog 2 (d + 1)`. The box prints the divisor `exp(beta)`,
whereas proof Step 5 explicitly gives `4 * exp(beta)`; use the latter. Logarithms remain
base 2 and the matrix exponential remains the natural exponential.

The printed `epsBE = (eps / (8 * log_2(1/eps)))^2` is retained. Equation (III.2)
requires a quantitative degree bound absent from the printed big-O estimate; this is
an unresolved proof gap, not an extra hypothesis or a field of the construction.
The p.9 `n_rho = poly(n)` convention is a family access convention; this query-only
statement keeps its actual ancillary size and asserts no gate-time bound. -/
theorem quantumEsscherTransform_implementation :
    ∃ Cdensity Cobservable : ℝ, 0 < Cdensity ∧ 0 < Cobservable ∧
      ∃ overhead : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
        ∀ P : PublicParameters, P.eps ≤ eps0 →
          ∃ construction : Construction P,
            (construction.circuit.queryCount 0 : ℝ) ≤
              Cdensity * P.kappa * (Real.logb 2 P.eps⁻¹) ^ 2 *
                max 1 (Real.logb 2 (2 + P.kappa * (Real.logb 2 P.eps⁻¹) ^ 2)) ^ overhead ∧
            (∀ j : Fin P.d, (construction.circuit.queryCount j.succ : ℝ) ≤
              Cobservable * Real.logb 2 P.eps⁻¹) ∧
            ∀ (input : InputData P)
              (purification : Matrix.unitaryGroup (Qubits (P.purificationAncillas + P.n)) ℂ),
              IsPurifiedAccess (a := P.purificationAncillas) input.rho
                (purification : Matrix (Qubits (P.purificationAncillas + P.n))
                  (Qubits (P.purificationAncillas + P.n)) ℂ) →
              ∀ O : (k : Fin (P.d + 1)) →
                  Matrix (Qubits (externalWidths P k)) (Qubits (externalWidths P k)) ℂ,
                O 0 = purifiedDensitySignal P purification →
                (∀ j : Fin P.d, IsQubitBlockEncoding P.observableAncillas P.n
                  (castOperator (by simp [externalWidths]) (O j.succ))
                  1 P.encodingError (input.H j)) →
                IsQubitBlockEncoding P.outputAncillas P.n (construction.circuit.unitary O)
                  1 P.eps (subnormalizedTransform P input) := by sorry

end QAlgorithms.Papers.RoadmapA09
