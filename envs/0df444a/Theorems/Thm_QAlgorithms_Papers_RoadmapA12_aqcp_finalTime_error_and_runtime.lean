-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA12_aqcp_finalTime_error_and_runtime
-- name    : QAlgorithms.Papers.RoadmapA12.aqcp_finalTime_error_and_runtime
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:03:01.125101+00:00
-- url     : https://prove2.me/theorems/cd723ae3-9ee9-47e8-97ac-0d2f31a067eb
-- title:
--   AQC(p): final-time error and sufficient runtime for positive definite linear systems
-- statement:
--   Let $n\in\mathbb N$, $N=2^n$, and let $A\in\mathbb C^{N\times N}$ be Hermitian positive definite with $\|A\|_2=1$. Let $b\in\mathbb C^N$ be a unit vector. Here $\|\cdot\|_2$ denotes the operator norm for matrices and the Euclidean norm for vectors. Write
--   $$
--   \kappa=\|A\|_2\|A^{-1}\|_2,\qquad
--   x=\frac{A^{-1}b}{\|A^{-1}b\|_2},\qquad
--   \widetilde x=|0\rangle\otimes x.
--   $$
--   The condition number is the actual value determined by $A$, and satisfies $\kappa\ge1$.
--
--   Set $Q_b=I-|b\rangle\langle b|$ and
--   $$
--   H_0=\begin{pmatrix}0&Q_b\\Q_b&0\end{pmatrix},\qquad
--   H_1=\begin{pmatrix}0&AQ_b\\Q_bA&0\end{pmatrix}.
--   $$
--   For $p>0$, AQC($p$) uses the schedule $f_p:[0,1]\to[0,1]$ specified by
--   $$
--   f_p'(s)=c_p(1-f_p(s)+f_p(s)/\kappa)^p,\quad f_p(0)=0,\qquad
--   c_p=\int_0^1(1-u+u/\kappa)^{-p}\,du.
--   $$
--   Thus $f_p(1)=1$. The schedule is $f_p(s)=s$ when $\kappa=1$; when $\kappa>1$ and $p=1$, it is $\kappa(1-\kappa^{-s})/(\kappa-1)$; otherwise it is the closed formula in Eq. (6). For positive runtime $T$, the normalized evolution $\psi_T:[0,1]\to\mathbb C^{2N}$ solves
--   $$
--   \psi_T'(s)=-iT[(1-f_p(s))H_0+f_p(s)H_1]\psi_T(s),\qquad
--   \psi_T(0)=|0\rangle\otimes b.
--   $$
--
--   For every fixed $p\in(1,2)$ there is a constant $C_p>0$, independent of $n,A,b,\kappa,T$ and the requested accuracy, such that this evolution exists for every $T>0$ and every solution satisfies
--   $$
--   \bigl\||\psi_T(1)\rangle\langle\psi_T(1)|
--         -|\widetilde x\rangle\langle\widetilde x|\bigr\|_2
--   \le \frac{C_p\kappa}{T}.
--   $$
--   Consequently, for every $\epsilon>0$ there exists a successful positive runtime $T\le C_p\kappa/\epsilon$: the evolution exists at this runtime and every solution has the displayed error at most $\epsilon$.
--
--   For each endpoint $p\in\{1,2\}$ there are constants $C_p>0$ and $\kappa_{0,p}\ge2$, independent of all input data and accuracy, such that whenever $\kappa\ge\kappa_{0,p}$ and $\epsilon>0$, there exists a positive runtime with
--   $$
--   T\le \frac{C_p\kappa\log\kappa}{\epsilon}
--   $$
--   at which the evolution exists and every solution has operator norm error at most $\epsilon$.
--
--   This result establishes the runtime and accuracy guarantee for the continuous AQC($p$) linear-system solver with positive definite matrices.
--
--   **Formalization Note** The error compares density matrices on the full $2N$-dimensional register. The endpoint big-O clause is asymptotic in $\kappa$; the threshold avoids interpreting $\kappa\log\kappa=0$ at $\kappa=1$ as an upper bound on a positive runtime. The frozen condition-number range binder is automatic on the stated input class.
-- source:
--   Quantum linear system solver based on time-optimal adiabatic quantum computing and quantum approximate optimization algorithm, arXiv:1909.05500v3, Theorem 1, Section 3, Eq. (7), PDF p. 5. https://arxiv.org/abs/1909.05500v3 . PDF SHA-256: 789fa02077bbb6baccb6f6f96088a62fff52b1807da8e98b19d9d3bb1490046e.

import Definitions.Def_QAlgorithms_Defs_AQCSchedules
import Definitions.Def_QAlgorithms_Papers_RoadmapA12_Model
set_option autoImplicit false

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.RoadmapA12


/-- An--Lin, arXiv:1909.05500v3, Theorem 1, PDF p.5 (printed 5:5),
with the standing assumptions of pp.1,3--4 and the endpoint runtime clause.
For each fixed `1 < p < 2`, a positive constant independent of the input and runtime
bounds the final density-matrix error by `C * conditionNumber A / T`, and a positive
runtime of at most `C * conditionNumber A / eps` suffices. For `p = 1` or `p = 2`,
the sufficient runtime is `O(conditionNumber A * log(conditionNumber A) / eps)`.
The endpoint big-O is asymptotic in the condition number, with a uniform threshold
at least 2; it is not a pointwise positive-runtime bound at condition number 1.
The frozen schedule completes Eq.(6) using Eq.(5): `f(s)=s` when the condition
number is 1 and the logarithmic-limit schedule when `p=1`. Appendix D's rescaled
gap gives the same schedule. `hk` is the condition-number range required by the
frozen schedule, automatic for these nonempty positive definite matrices.
Existence of each source IVP is asserted, so the error clauses are nonvacuous. -/
theorem aqcp_finalTime_error_and_runtime :
    (∀ (p : ℝ) (hp : 1 < p), p < 2 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (A : Matrix (Qubits n) (Qubits n) ℂ) (hA : A.PosDef),
          specNorm A = 1 →
          ∀ (b : EuclideanSpace ℂ (Qubits n)) (hb : IsState b)
            (hk : 1 ≤ conditionNumber A),
          (∀ T : ℝ, 0 < T →
            (∃ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
              AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi) ∧
            ∀ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
              AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi →
                finalError A b psi ≤ C * conditionNumber A / T) ∧
          (∀ eps : ℝ, 0 < eps →
            ∃ T : ℝ, 0 < T ∧ T ≤ C * conditionNumber A / eps ∧
              (∃ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi) ∧
              ∀ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p (lt_trans zero_lt_one hp) T psi →
                  finalError A b psi ≤ eps)) ∧
    (∀ (p : ℝ) (hp : 0 < p), p = 1 ∨ p = 2 →
      ∃ C : ℝ, 0 < C ∧ ∃ kappa0 : ℝ, 2 ≤ kappa0 ∧
        ∀ (n : ℕ) (A : Matrix (Qubits n) (Qubits n) ℂ) (hA : A.PosDef),
          specNorm A = 1 →
          ∀ (b : EuclideanSpace ℂ (Qubits n)) (hb : IsState b)
            (hk : 1 ≤ conditionNumber A),
          kappa0 ≤ conditionNumber A →
          ∀ eps : ℝ, 0 < eps →
            ∃ T : ℝ, 0 < T ∧
              T ≤ C * conditionNumber A * Real.log (conditionNumber A) / eps ∧
              (∃ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p hp T psi) ∧
              ∀ psi : ℝ → EuclideanSpace ℂ (Bool × Qubits n),
                AQCP.IsRun A hA b hb hk p hp T psi → finalError A b psi ≤ eps) := by sorry

end QAlgorithms.Papers.RoadmapA12
