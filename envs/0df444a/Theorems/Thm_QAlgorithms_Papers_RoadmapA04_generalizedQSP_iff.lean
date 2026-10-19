-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA04_generalizedQSP_iff
-- name    : QAlgorithms.Papers.RoadmapA04.generalizedQSP_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:16:11.985899+00:00
-- url     : https://prove2.me/theorems/93e357e1-95b1-4842-949e-aa752a587454
-- title:
--   Generalized quantum signal processing: exact characterization of polynomial pairs
-- statement:
--   Let $d\in\mathbb N$ and let $P,Q\in\mathbb C[x]$ be prescribed ordinary complex polynomials. For real angles define
--   $$
--   R(\theta,\phi,\lambda)=
--   \begin{pmatrix}
--   e^{i(\lambda+\phi)}\cos\theta & e^{i\phi}\sin\theta\\
--   e^{i\lambda}\sin\theta & -\cos\theta
--   \end{pmatrix}.
--   $$
--   For any positive integer $N$ and any unitary $N\times N$ matrix $U$, put $A(U)=\operatorname{diag}(U,I_N)$, with the control qubit as the first tensor factor, and
--   $$
--   S_d(U)=(R(\theta_d,\phi_d,0)\otimes I_N)A(U)\cdots
--   (R(\theta_1,\phi_1,0)\otimes I_N)A(U)
--   (R(\theta_0,\phi_0,\lambda)\otimes I_N).
--   $$
--   When $d=0$, this is just the initial rotation tensored with $I_N$. There exist real vectors $\theta,\phi\in\mathbb R^{d+1}$ and a real $\lambda$, chosen independently of $N$ and $U$, such that
--   $$
--   S_d(U)=
--   \begin{pmatrix}
--   P(U)& *\\
--   Q(U)& *
--   \end{pmatrix}
--   \quad\text{for every }N\ge 1\text{ and every unitary }U
--   $$
--   if and only if
--   $$
--   \deg P\le d,\qquad \deg Q\le d,\qquad
--   |P(z)|^2+|Q(z)|^2=1\quad\text{for every }z\in\mathbb C\text{ with }|z|=1.
--   $$
--   Here $P(U)$ and $Q(U)$ denote polynomial evaluation at the matrix $U$, and the stars leave the second-column blocks unspecified. The zero polynomial satisfies the degree bound.
--
--   This theorem characterizes exactly the polynomial pairs synthesized by $d$ forward signal applications and $d+1$ rotations; it imposes no real-coefficient or parity restriction.
--
--   **Formalization Note** Universal finite-dimensional unitary realization expresses the polynomial identity used by the proof; in particular, it includes every scalar unitary $U=[z]$. The rotation is the matrix printed in equation (6), without a determinant-one constraint.
-- source:
--   Generalized Quantum Signal Processing, arXiv:2308.01501v2, Theorem 3 (Generalized Quantum Signal Processing), Section III, equation (7), PDF p. 4. https://arxiv.org/abs/2308.01501v2 . PDF SHA-256: 580bebd31f91f41b7b0790d4e82eb2a93a30ea872397c78be90ab3f958ce2af6.

import Definitions.Def_QAlgorithms_Defs_GeneralizedQSP
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapA04

/-- Motlagh and Wiebe, *Generalized Quantum Signal Processing*, arXiv:2308.01501v2,
Theorem 3, equation (7), PDF p.4 (signal and rotation: equations (5)--(6), PDF p.3).
For prescribed complex polynomials, exact first-column realization by one set of real angles
for every finite-dimensional unitary is equivalent to the degree bounds and normalization
on the entire unit circle. The sequence is R_d A ... R_1 A R_0, with A = diag(U,I).
Equation (6), rather than the reverse-proof base-case prose typo, fixes Q = exp(i lambda) sin theta.
The printed rotations are unitary; no determinant-one condition or phase adjustment is imposed. -/
theorem generalizedQSP_iff (d : ℕ) (P Q : Polynomial ℂ) :
    (∃ theta phi : Fin (d + 1) → ℝ, ∃ lam : ℝ,
      ∀ N : ℕ, 0 < N → ∀ U : Matrix (Fin N) (Fin N) ℂ,
        U ∈ Matrix.unitaryGroup (Fin N) ℂ → ∀ i j : Fin N,
          gqspSequence theta phi lam U (false, i) (false, j) =
            (Polynomial.aeval U P) i j ∧
          gqspSequence theta phi lam U (true, i) (false, j) =
            (Polynomial.aeval U Q) i j) ↔
      P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by sorry

end QAlgorithms.Papers.RoadmapA04
