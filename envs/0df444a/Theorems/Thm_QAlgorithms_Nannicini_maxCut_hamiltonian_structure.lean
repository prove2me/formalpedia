-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_maxCut_hamiltonian_structure
-- name    : QAlgorithms.Nannicini.maxCut_hamiltonian_structure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:57.46637+00:00
-- url     : https://prove2.me/theorems/e95e0b77-fcbf-4a9a-8a96-c0a87c5bc9bd
-- title:
--   The MaxCut mirror-descent Hamiltonians are y₁Ĉ + y₂D with ‖y‖₁ ≤ (4/ϵ) log n
-- statement:
--   Let $C\in\mathbb R^{n\times n}$ be a nonzero symmetric matrix, $\hat C=C/\|C\|_F$, $\gamma\in[-1,1]$, $\epsilon>0$, $\eta=\epsilon/16$ and $T=\lceil(64/\epsilon^2)\log_2 n\rceil$. Run Alg. 6 as in §8.4.2: for $\tau=1,\dots,T-1$, the subgradient $G^{(\tau)}$ is the output of the estimate-driven procedure (equal to $0$, to $-\hat C$, or to a diagonal matrix with entries in $\{-1,0,1\}$) applied to estimates $\widetilde c_\tau,\widetilde d_\tau$ with $|\widetilde c_\tau-\operatorname{Tr}(\hat C\rho^{(\tau)})|\le\epsilon/4$ and $\sum_j|\widetilde d_{\tau,j}-\rho^{(\tau)}_{jj}|\le\epsilon/4$, where $\rho^{(\tau)}$ is the Gibbs state of $H^{(\tau)}$ and
--
--   $$H^{(t)}=-\eta\sum_{\tau=1}^{t-1}G^{(\tau)}.$$
--
--   Then for every $t=1,\dots,T$ there are $y\in\mathbb R^2$ and a diagonal matrix $D$ with $|D_{jj}|\le1$ for all $j$ such that
--
--   $$H^{(t)}=y_1\hat C+y_2D,\qquad \|y\|_1=|y_1|+|y_2|\le\frac{4}{\epsilon}\log_2 n.$$
--
--   This structure is what makes the Hamiltonians block-encodable by a linear combination of two block-encodings with subnormalization $\|y\|_1$.
--
--   **Formalization Note** The normalization $|D_{jj}|\le1$, which the proof imposes, is part of the conclusion, since otherwise the bound on $\|y\|_1$ could be met by rescaling $D$. $T$ is the ceiling as in Theorem 8.30.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 204, Lemma 8.33. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP




/-- Nannicini p.204, Lemma 8.33. For every iteration `t` of Alg. 6 applied to (MaxCutSDP-F) as
described in Sect. 8.4.2, `H^(t) = y_1 Ĉ + y_2 D` for some vector `y ∈ ℝ²`, where `D` is a
diagonal matrix. Furthermore, `‖y‖_1 ≤ (4/ϵ) log n`.

The run of §8.4.2: `η = ϵ/16`, `T = ⌈(64/ϵ²) log₂ n⌉` (ceiling as in Theorem 8.30), and for
`τ = 1, …, T − 1` the subgradient `G^(τ)` is the estimate-driven matrix `maxCutSubgrad`
computed from estimates `estC τ`, `estD τ` of `Tr(Ĉρ^(τ))`, `ρ^(τ)_jj` satisfying Eq. (8.27), with
`ρ^(τ) = mmwuIterate η G τ`. The Hamiltonian is `H^(t) = −η Σ_{τ<t} G^(τ)` (Prop. 8.7, Alg. 6), for
`t = 1, …, T`. The normalization `|D_jj| ≤ 1` (proof, p.204: "we can keep `D` normalized so that its
entries are less than 1 in absolute value") is part of the conclusion: without it the bound on
`‖y‖_1` says nothing. -/
theorem maxCut_hamiltonian_structure {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (estC : ℕ → ℝ) (estD : ℕ → Fin n → ℝ)
    (hest : ∀ τ, 1 ≤ τ → τ < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      |estC τ - (cHat (C.map ((↑) : ℝ → ℂ)) *
          mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ).trace.re|
          ≤ ε * 4⁻¹ ∧
        ∑ j, |estD τ j - (mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ j j).re|
          ≤ ε * 4⁻¹)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊) :
    ∃ (y : Fin 2 → ℝ) (d : Fin n → ℂ), (∀ j, ‖d j‖ ≤ 1) ∧
      -((ε * 16⁻¹ : ℝ) : ℂ) • ∑ τ ∈ Finset.Ico 1 t,
          maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC τ) (estD τ) =
        ((y 0 : ℝ) : ℂ) • cHat (C.map ((↑) : ℝ → ℂ)) + ((y 1 : ℝ) : ℂ) • Matrix.diagonal d ∧
      |y 0| + |y 1| ≤ 4 * ε⁻¹ * Real.logb 2 n := by
  sorry

















end QAlgorithms.Nannicini
