-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_phaseEstimation_exact
-- name    : QAlgorithms.DeWolf.phaseEstimation_exact
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:33:46.368073+00:00
-- url     : https://prove2.me/theorems/0bb1ea64-42fe-4800-a818-756a56d6f426
-- title:
--   Phase estimation returns an exactly n-bit phase with probability 1
-- statement:
--   Let $U$ be a unitary matrix acting on a finite-dimensional space, and let $|\psi\rangle$ be a unit eigenvector of $U$ with eigenvalue $e^{2\pi i\varphi}$, where $\varphi\in[0,1)$:
--
--   $$
--   U|\psi\rangle=e^{2\pi i\varphi}|\psi\rangle .
--   $$
--
--   Fix $n\ge0$, put $N=2^n$, and suppose $\varphi$ can be written exactly with $n$ bits, i.e. $2^n\varphi=k$ for a natural number $k$ (necessarily $k<N$). Run phase estimation: start in $|0^n\rangle|\psi\rangle$, apply the quantum Fourier transform $F_N$ to the first $n$ qubits, apply the controlled power $|j\rangle|\psi\rangle\mapsto|j\rangle U^j|\psi\rangle$, then apply $F_N^{-1}=F_N^{*}$ to the first $n$ qubits and measure them in the computational basis (bit strings read most significant bit first). Then
--
--   1. after the controlled power the state is $\big(F_N|k\rangle\big)\otimes|\psi\rangle$, i.e. $\frac{1}{\sqrt N}\sum_{j=0}^{N-1}e^{2\pi i\varphi j}|j\rangle|\psi\rangle=F_N|2^n\varphi\rangle|\psi\rangle$;
--   2. the measurement of the first register yields the outcome $k=2^n\varphi=\varphi_1\dots\varphi_n$ with probability $1$.
--
--   This is the exact case of phase estimation, the subroutine underlying Shor's algorithm, quantum counting and many Hamiltonian algorithms.
--
--   **Formalization Note** The final state is the shared `phaseEstimationState`, $(F_N^{*}\otimes I)\,\Lambda(U)\,(F_N\otimes I)\,|0^n\rangle|\psi\rangle$ with $\Lambda(U)|j\rangle|\phi\rangle=|j\rangle U^{j}|\phi\rangle$; the probability of outcome $k$ on the first register is the marginal $\sum_b|\langle k,b|\cdot\rangle|^2$. The source's general-case claim (an $n$-bit approximation with additive error $O(2^{-n})$ 'with high probability') supplies no probability constant and is not stated.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 46, §4.6. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace QAlgorithms.DeWolf


/-- de Wolf §4.6, PDF pp.45–46 (unnumbered): phase estimation in the exact case. Let `U` be a
unitary with eigenvector `ψ` (a unit vector), `U ψ = e^{2πiϕ} ψ`, `ϕ ∈ [0, 1)`, and suppose `ϕ`
has an exact `n`-bit expansion, `2^n ϕ = k ∈ ℕ`. Then after step 3 (applying `F_N`, `N = 2^n`, to
the first register of `|0^n⟩|ψ⟩` and then `|j⟩|ψ⟩ ↦ |j⟩ U^j |ψ⟩`) the state is
`F_N |2^n ϕ⟩ ⊗ |ψ⟩`, and after step 4 (`F_N^{-1} = F_N^*` on the first register) measuring the
first register yields `|2^n ϕ⟩ = |k⟩` with probability 1. -/
theorem phaseEstimation_exact {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (U : Matrix κ κ ℂ) (hU : U ∈ Matrix.unitaryGroup κ ℂ)
    (ψ : EuclideanSpace ℂ κ) (hψ : IsState ψ)
    (ϕ : ℝ) (hϕ0 : 0 ≤ ϕ) (hϕ1 : ϕ < 1)
    (heig : act U ψ = Complex.exp (2 * Real.pi * Complex.I * ϕ) • ψ)
    (k : ℕ) (hk : (2 : ℝ) ^ n * ϕ = k) :
    act (controlledPower n U * Matrix.kronecker (qftQubits n) (1 : Matrix κ κ ℂ))
        (tensorVec (zeroKet n) ψ) =
      tensorVec (act (qftQubits n) (ket (natToBits n k))) ψ ∧
    marginalFst (phaseEstimationState n U ψ) (natToBits n k) = 1 := by
  sorry

end QAlgorithms.DeWolf
