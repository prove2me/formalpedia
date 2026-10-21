-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_covariant_two_channel_decomposition
-- name    : QAlgorithms.Papers.Independent.Support21.P18.covariant_two_channel_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:52:51.607981+00:00
-- url     : https://prove2.me/theorems/f50fcf9a-b8c5-4a05-88b3-7e6076889bd2
-- title:
--   The two concrete covariant extremal channels
-- statement:
--   Fix $N\ge1$. Write $|k\rangle_n$ for the normalized occupation basis of the symmetric $n$-qubit space. Define maps to a physical qubit and an environment by
--   $$
--   V_-|k\rangle_N=\sqrt{\frac{N-k}{N}}|0\rangle|k\rangle_{N-1}+\sqrt{\frac kN}|1\rangle|k-1\rangle_{N-1},
--   $$
--   $$
--   V_+|k\rangle_N=\sqrt{\frac{k+1}{N+2}}|0\rangle|k+1\rangle_{N+1}-\sqrt{\frac{N-k+1}{N+2}}|1\rangle|k\rangle_{N+1},
--   $$
--   where out-of-range terms with zero coefficient are omitted. These maps are isometries and intertwine $D_N(U)$ with $U\otimes D_{N-1}(U)$ and $U\otimes D_{N+1}(U)$ respectively, for every $U\in SU(2)$. Define the physical covariant channels $T_\pm(\rho)=\operatorname{Tr}_{\mathrm{env}}(V_\pm\rho V_\pm^\dagger)$. On every input operator and qubit operator $A$, they satisfy Eq. (12): $\operatorname{Tr}[T_\pm(\rho)A]=\operatorname{Tr}[\rho V_\pm^\dagger(A\otimes I)V_\pm]$.
--
--   Every covariant CPTP map $T$ from the symmetric $N$-qubit space to a qubit admits some $t\in[0,1]$ such that
--   $$
--   T=tT_-+(1-t)T_+,\qquad\Delta(T)=t\Delta(T_-)+(1-t)\Delta(T_+).
--   $$
--   This is the concrete two-branch specialization of the covariant representation: the environment spins are $(N-1)/2$ and $(N+1)/2$.
--
--   Here $\Delta(S)=\max_{\|\psi\|=1}\operatorname{Tr}[|\psi\rangle\langle\psi|S(|\psi^{\otimes N}\rangle\langle\psi^{\otimes N}|)]$ is the worst-case overlap with the original state, so the corresponding worst-case complement fidelity is $1-\Delta(S)$.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 4, Optimality proof, Eqs.(11),(12): two extremal covariant channels

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.4, Eqs.(11),(12): concrete spin-(N-1)/2 and spin-(N+1)/2 isometries
intertwine the specified SU(2) tensor actions and give the two extremal channels.
The convex decomposition is equality on every operator, hence every input state. -/
theorem covariant_two_channel_decomposition (N : ℕ) (hN : 1 ≤ N) :
    (lowerIsometry N)ᴴ * lowerIsometry N = 1 ∧
    (upperIsometry N)ᴴ * upperIsometry N = 1 ∧
    (∀ U : Matrix.unitaryGroup (Fin 2) ℂ, Matrix.det U.val = 1 →
      Matrix.kronecker U.val (symmetricAction (N - 1) U.val) * lowerIsometry N =
        lowerIsometry N * symmetricAction N U.val ∧
      Matrix.kronecker U.val (symmetricAction (N + 1) U.val) * upperIsometry N =
        upperIsometry N * symmetricAction N U.val) ∧
    IsChannel (lowerChannel N) ∧ IsUniversallyCovariant N (lowerChannel N) ∧
    IsChannel (upperChannel N) ∧ IsUniversallyCovariant N (upperChannel N) ∧
    (∀ (rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ),
      (lowerChannel N rho * A).trace =
        (rho * (lowerIsometry N)ᴴ * Matrix.kronecker A
          (1 : Matrix (SymmetricBasis (N - 1)) (SymmetricBasis (N - 1)) ℂ) * lowerIsometry N).trace ∧
      (upperChannel N rho * A).trace =
        (rho * (upperIsometry N)ᴴ * Matrix.kronecker A
          (1 : Matrix (SymmetricBasis (N + 1)) (SymmetricBasis (N + 1)) ℂ) * upperIsometry N).trace) ∧
    (∀ T : Superop (SymmetricBasis N) (Fin 2), IsChannel T → IsUniversallyCovariant N T →
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        (∀ rho, T rho = (t : ℂ) • lowerChannel N rho + ((1 - t : ℝ) : ℂ) • upperChannel N rho) ∧
        notError N T = t * notError N (lowerChannel N) +
          (1 - t) * notError N (upperChannel N)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
