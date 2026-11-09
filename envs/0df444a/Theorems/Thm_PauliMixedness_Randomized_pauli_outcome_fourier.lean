-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_pauli_outcome_fourier
-- name    : PauliMixedness.Randomized.pauli_outcome_fourier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:49.545107+00:00
-- url     : https://prove2.me/theorems/b8eb9a84-2214-4ece-944e-e9d012296b71
-- title:
--   Observation 2.3 — Fourier expansion of physical Pauli outcomes
-- statement:
--   For $N\ge1$, a complex density matrix $\rho$, a product Pauli setting $P$ and any sign outcome $x$, let $r_{\rho,P}(x)=\operatorname{Re}\operatorname{Tr}(M_x^P\rho)$ be its physical Born mass. Then both equalities hold:
--
--   $$r_{\rho,P}(x)=2^{-N}\sum_{S\subseteq[N]}\operatorname{Tr}(P^S\rho)\chi_S(x),$$
--   $$r_{\rho,P}(x)=2^{-N}+2^{-N}\sum_{S\ne\varnothing}\alpha_P(S)\chi_S(x).$$
--
--   The first equality is an equality in the complex numbers, identifying the real mass with its complex embedding; the second is real. This connects the independently defined physical outcome law with its Fourier representation, including the identity contribution.
--
--   Differences from the source:
--   - reading: the measured state is named $\sigma$ in prose and $\rho$ in the traces → one measured state $\rho$ in both formulas; reason: the passage describes one outcome law; using unrelated states would make the assertion false
--   - encoding: sign strings in $\{-1,1\}^N$ and one-based wires → $\mathbb F_2^N$ with sign $(-1)^b$ and zero-based finite wires; reason: bijective reindexing preserves every outcome, character and state
--   - encoding: real probabilities equated with Hermitian traces → the first equality embeds the real Born mass in ℂ and retains the complex traces; the second uses their real parts; reason: Pauli traces of density matrices are real, so both original equalities are preserved
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Observation 2.3 p.6; Observation 3.2 pp.10–11

import Definitions.Def_PauliMixedness_Randomized_QuantumModel

open scoped BigOperators

namespace PauliMixedness.Randomized

/-- Observation 2.3 p.6. σ and ρ in the source denote the same measured state.
Both equalities are retained, including the complex trace equality. -/
theorem pauli_outcome_fourier (N : ℕ) (hN : 1 ≤ N)
    (ρ : Operator N) (hρ : QAlgorithms.IsDensityMatrix ρ) (P : Setting N) (x : Cube N) :
    (outcomeMass ρ P x : ℂ) = ((2 : ℂ)^N)⁻¹ *
      ∑ S : Finset (Fin N), (pauliOn P S * ρ).trace * (chi S x : ℂ) ∧
    outcomeMass ρ P x = ((2 : ℝ)^N)⁻¹ + ((2 : ℝ)^N)⁻¹ *
      ∑ S : Finset (Fin N), if S = ∅ then 0 else basisCoeff ρ P S * chi S x := by sorry

end PauliMixedness.Randomized
