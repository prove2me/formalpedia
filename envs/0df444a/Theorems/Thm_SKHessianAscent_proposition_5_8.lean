-- Prove2me | Theorems.Thm_SKHessianAscent_proposition_5_8
-- name    : SKHessianAscent.proposition_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:16:23.112974+00:00
-- url     : https://prove2.me/theorems/b833f8bf-f262-495b-9901-9fdaa78d9b7c
-- title:
--   Proposition 5.8 — the expected reciprocal extension is within $O(1/n)$ of its free limit $\mathbf E_{M_n}[D(aI_n-\beta S+D)^{-2}D]$
-- statement:
--   Let $S$ be a semicircular element free from $(M_n(\mathbb C),\mathrm{tr}_n)$ in $(\mathcal M_n,\tau_n)$ and $\mathbf E_{M_n}$ the trace-preserving conditional expectation onto $M_n(\mathbb C)$. There is a universal constant $C>0$ such that the following holds. Fix a real diagonal $D\succeq I_n$, $a\in[0,1]$, $\beta>0$, $\gamma_Y>0$, and suppose that the spectral gap condition in the free limit
--   $$(I_n+D^{-1}(aI_n-\beta S))(I_n+(aI_n-\beta S)D^{-1})\succeq4\gamma_YI_n\tag{5.32}$$
--   holds in $\mathcal M_n$. Then, with $\phi$ the reciprocal extension (5.1) for the cutoff $\gamma_Y$ and $A\sim\mathrm{GOE}(n)$,
--   $$\Big\|\mathbf E_A\,\phi\big((I_n+D^{-1}(aI_n-\beta A))(I_n+(aI_n-\beta A)D^{-1})\big)-\mathbf E_{M_n}\big[D(aI_n-\beta S+D)^{-2}D\big]\Big\|_{\mathrm{op}}\le\frac Cn\big(\beta^2\gamma_Y^{-2}+\beta^4\gamma_Y^{-3}\big).\tag{5.33}$$
--   In particular, for every real diagonal $T$, with $W=D^{-1}$,
--   $$\Big|\mathbf E_A\,\Phi_{a,W,T}(A)-\tau_n\big[TD(aI_n-\beta S+D)^{-2}D\big]\Big|\le\frac Cn\big(\beta^2\gamma_Y^{-2}+\beta^4\gamma_Y^{-3}\big)\|T\|_{L^2}.\tag{5.34}$$
--
--   **Formalization Note** $(aI_n-\beta S+D)^{-2}$ is the square of the inverse in $M_n(\mathcal A)$ (`Ring.inverse`), and $\tau_n[TX]=\mathrm{tr}_n(T\,\mathbf E_{M_n}[X])$ for a scalar matrix $T$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §5.3, Proposition 5.8, (5.32)–(5.34), p. 34

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal
import Definitions.Def_SKHessianAscent_FreeModel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace SKHessianAscent

theorem proposition_5_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (d : Fin n → ℝ) (a β γ : ℝ), (∀ i, 1 ≤ d i) → 0 ≤ a → a ≤ 1 → 0 < β → 0 < γ →
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (s : GueIdx n → H →L[ℂ] H) (ω : H), FreeWeaver.Walk.IsStdFreeSemicircular s ω →
          let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ)
          let Di : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => ((d i : ℂ))⁻¹
          SpecGe (gueOp (1 + (a : ℂ) • Di) (-(β : ℂ) • Di) 1 s *
            gueOp (1 + (a : ℂ) • Di) (-(β : ℂ) • 1) Di s) (4 * γ) →
          let EA : Matrix (Fin n) (Fin n) ℂ := fun i j =>
            ((∫ A, matFun (phi γ) (reciprocalArg β a (fun i => (d i)⁻¹) (Matrix.of A)) i j
              ∂(RandMatDisc.goe n) : ℝ) : ℂ)
          let F : Matrix (Fin n) (Fin n) ℂ :=
            FreeWeaver.Walk.slice ω (gueOp D 0 1 s *
              Ring.inverse (gueOp ((a : ℂ) • 1 + D) (-(β : ℂ) • 1) 1 s) ^ 2 * gueOp D 0 1 s)
          FreeWeaver.Walk.opNorm (EA - F) ≤
              C / n * (β ^ 2 * γ ^ (-2 : ℤ) + β ^ 4 * γ ^ (-3 : ℤ)) ∧
            ∀ τ : Fin n → ℝ,
              ‖((∫ A, PhiFun β γ a (fun i => (d i)⁻¹) τ (Matrix.of A) ∂(RandMatDisc.goe n) : ℝ) : ℂ) -
                  (1 / (n : ℂ)) * (Matrix.diagonal (fun i => (τ i : ℂ)) * F).trace‖ ≤
                C / n * (β ^ 2 * γ ^ (-2 : ℤ) + β ^ 4 * γ ^ (-3 : ℤ)) *
                  Real.sqrt ((∑ i, τ i ^ 2) / n) := by sorry

end SKHessianAscent
