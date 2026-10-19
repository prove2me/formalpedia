-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_genPicPolytope_sandwich
-- name    : QAlgorithms.Nannicini.genPicPolytope_sandwich
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:52:48.069538+00:00
-- url     : https://prove2.me/theorems/e303801e-bd99-488d-ae2e-0743628484e4
-- title:
--   The generalized PIC polytope built from θ-accurate traces is sandwiched between P_0 and P_{4Rrθ}
-- statement:
--   Consider the SDP data of (P-SDP)/(D-SDP) (Hermitian $n\times n$ matrices $C, A^{(1)},\dots,A^{(m)}$, $b \in \mathbb{R}^m$) under the standing assumptions (a) $A^{(1)} = I$, $b_1 = R > 0$; (b) $\|C\| \le 1$; (c) (D-SDP) has an optimal solution $y$ with $\|y\|_1 \le r$, where $r \ge 1$. Fix $\gamma \in \mathbb{R}$. For $\epsilon \ge 0$ let $P_\epsilon(X)$ be the PIC polytope (8.16), and for $a \in \mathbb{R}^m$, $c \in \mathbb{R}$ let
--
--   $$
--   \hat P(a, c) = \Bigl\{ y \in \mathbb{R}^m : b^\top y \le \gamma,\ \textstyle\sum_j y_j \le r,\ \sum_j a_j y_j \ge c,\ y \ge 0 \Bigr\}.
--   $$
--
--   Let $X \succeq 0$ with $\operatorname{Tr}(X) \le R$, let $\rho = X/\operatorname{Tr}(X)$, let $\theta \ge 0$, and let $\tilde a \in \mathbb{R}^m$, $\tilde c \in \mathbb{R}$ satisfy
--
--   $$
--   |\operatorname{Tr}(C\rho) - \tilde c| \le \theta, \qquad |\operatorname{Tr}(A^{(j)}\rho) - \tilde a_j| \le \theta \quad (j = 1, \dots, m).
--   $$
--
--   Then
--
--   $$
--   P_0(X) \cap \{y : \|y\|_1 \le r\} \ \subseteq\ \hat P\bigl(\tilde a, \tilde c - (r+1)\theta\bigr) \ \subseteq\ P_{4Rr\theta}(X) \cap \{y : \|y\|_1 \le r\}.
--   $$
--
--   With $\theta = \epsilon/(12Rr)$ this lets a PIC oracle work from estimated trace values only, which is what the quantum MMWU solver provides.
--
--   **Formalization Note** Traces are taken as real parts. In Lean $0^{-1} = 0$, so at $X = 0$ the matrix $\rho$ is $0$; the chain of inclusions still holds in that case.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 192, Proposition 8.19. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

open scoped ComplexOrder





/-- Nannicini pp.192–193, Proposition 8.19 ([van Apeldoorn, 2020]). Standing assumptions:
(a) `A^(1) = I`, `b_1 = R > 0`; (b) `‖C‖ ≤ 1`; (c) some optimal solution of (D-SDP) has
`‖y‖₁ ≤ r`, with `r ≥ 1`. Let `X ⪰ 0`, `ρ = X / Tr(X)` with `Tr(X) ≤ R`, `θ ≥ 0`, and let
`ã ∈ ℝ^m`, `c̃ ∈ ℝ` with `|Tr(Cρ) − c̃| ≤ θ` and `|Tr(A^(j)ρ) − ã_j| ≤ θ` for all `j`. Then
`P_0(X) ∩ {‖y‖₁ ≤ r} ⊆ P̂(ã, c̃ − (r + 1)θ) ⊆ P_{4Rrθ}(X) ∩ {‖y‖₁ ≤ r}`.
At `X = 0` Lean's `0⁻¹ = 0` gives `ρ = 0`; the chain still holds there. -/
theorem genPicPolytope_sandwich {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ) (R r : ℝ)
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (hr : 1 ≤ r) (hopt : ∃ y : Fin m → ℝ, IsDualOptimal A C b y ∧ ∑ j, |y j| ≤ r)
    (γ : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) (hXR : X.trace.re ≤ R)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = (X.trace)⁻¹ • X)
    (θ : ℝ) (hθ : 0 ≤ θ) (atil : Fin m → ℝ) (ctil : ℝ)
    (hc : |(C * ρ).trace.re - ctil| ≤ θ) (ha : ∀ j, |(A j * ρ).trace.re - atil j| ≤ θ) :
    picPolytope A b C γ 0 X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} ⊆
        genPicPolytope b γ r atil (ctil - (r + 1) * θ) ∧
      genPicPolytope b γ r atil (ctil - (r + 1) * θ) ⊆
        picPolytope A b C γ (4 * R * r * θ) X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} := by
  sorry




end QAlgorithms.Nannicini
