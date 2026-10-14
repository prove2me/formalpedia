-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_qaoa_approximates_adiabatic
-- name    : QAlgorithms.Nannicini.qaoa_approximates_adiabatic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:50.862341+00:00
-- url     : https://prove2.me/theorems/52c231a1-473b-4494-a83c-18085d539d47
-- title:
--   QAOA with enough layers reaches a maximum eigenstate of H_F
-- statement:
--   Let $n \ge 0$ and let $f : \{0,1\}^n \to \mathbb{R}$ be the objective of the maximization problem (9.38). Define the $n$-qubit Hamiltonians
--
--   $$
--   H_F = \sum_{x \in \{0,1\}^n} f(x)\,|x\rangle\langle x|, \qquad H_I = \sum_{j=1}^n \sigma_j^X,
--   $$
--
--   where $\sigma_j^X$ is the Pauli $X$ on qubit $j$ and the identity elsewhere. For $p \ge 1$ and $\beta, \theta \in [0, 2\pi]^p$ let
--
--   $$
--   U_{\mathrm{QAOA}}(p, \beta, \theta) = e^{-i\beta_p H_I} e^{-i\theta_p H_F} \cdots e^{-i\beta_1 H_I} e^{-i\theta_1 H_F}.
--   $$
--
--   Then for every $\delta > 0$ there are a unit vector $|\varphi\rangle$ with $H_F|\varphi\rangle = (\max_x f(x))\,|\varphi\rangle$, that is an eigenstate of $H_F$ with maximum eigenvalue, and an integer $P \ge 1$ such that for every $p \ge P$ there are angles $\beta^*, \theta^* \in [0, 2\pi]^p$ with
--
--   $$
--   \bigl\| U_{\mathrm{QAOA}}(p, \beta^*, \theta^*)\,(H|0\rangle)^{\otimes n} - |\varphi\rangle \bigr\| \le \delta .
--   $$
--
--   Here $(H|0\rangle)^{\otimes n}$ is the uniform superposition, the maximum eigenstate of $H_I$. The proposition says that with enough layers, the QAOA ansatz can reproduce adiabatic evolution along $H(s) = (1-s)H_I + sH_F$ and so prepares a state close to one encoding an optimal solution of (9.38).
--
--   **Formalization Note** The source's limit over $p$, with angles that depend on $p$, is stated as "for all sufficiently large $p$ some angles achieve distance at most $\delta$", with the target eigenvector fixed before $p$. The global phase allowed by Theorem 9.11 is absorbed into the choice of the eigenvector, since a phase multiple of a maximum eigenvector is again one. The informal claim that $U_{\mathrm{QAOA}}$ "approximates an adiabatic evolution" is represented by its stated "in particular" consequence.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 230, Proposition 9.28. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

universe u

namespace QAlgorithms.Nannicini




/-- Nannicini p.230, Proposition 9.28. Consider the time-dependent Hamiltonian
`H(s) = (1 − s)H_I + sH_F` (9.41), where `H_F = Σ_x f(x)|x⟩⟨x|` (9.39) and `H_I = Σ_j σ_j^X`
(9.40). For `p ∈ ℕ`, `p > 0`, let `β, θ ∈ [0, 2π]^p`, and define
`U_QAOA(p, β, θ) := e^{−iβ_p H_I} e^{−iθ_p H_F} ⋯ e^{−iβ_1 H_I} e^{−iθ_1 H_F}` (9.42). Then, for any
`δ > 0` and for `p → ∞`, there exists a choice `β*, θ*` of `β, θ` such that `U_QAOA(p, β*, θ*)`
approximates an adiabatic evolution of `H(s)`, and in particular
`lim_{p→∞} ‖U_QAOA(p, β*, θ*)(H|0⟩)^{⊗n} − |φ(1)⟩‖ ≤ δ`, where `|φ(1)⟩` is an eigenstate of
`H(1) = H_F` with maximum eigenvalue, encoding a solution to problem (9.38).

`f : {0,1}^n → ℝ` is arbitrary (problem (9.38)); `H_F` is the frozen `problemHamiltonian f`,
`H_I` the frozen `qaoaMixer n`, `U_QAOA` the frozen `qaoaUnitary f p β θ` (index `k : Fin p` is the
source's `k + 1`; the first factor applied is `e^{−iθ_1 H_F}`). The maximum eigenvalue of `H_F` is
`max_x f(x)`. The limit claim, with angles depending on `p`, is stated as: for every `δ > 0` there
are a unit eigenvector `φ` of `H_F` with eigenvalue `max f` and a `P ≥ 1` such that for every
`p ≥ P` some angles in `[0, 2π]^p` bring the QAOA state within `δ` of `φ`. The global phase of
Thm. 9.11 is absorbed into `φ` (a phase multiple of a top eigenvector is one). The informal
"approximates an adiabatic evolution" is the "in particular" claim, which is what is stated. -/
theorem qaoa_approximates_adiabatic {n : ℕ} (f : Qubits n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : EuclideanSpace ℂ (Qubits n), IsState φ ∧
      act (problemHamiltonian f) φ = ((Finset.univ.sup' Finset.univ_nonempty f : ℝ) : ℂ) • φ ∧
      ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
        ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          ‖act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - φ‖ ≤ δ := by
  sorry

end QAlgorithms.Nannicini
