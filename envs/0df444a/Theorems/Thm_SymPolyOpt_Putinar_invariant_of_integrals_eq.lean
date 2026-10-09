-- Prove2me | Theorems.Thm_SymPolyOpt_Putinar_invariant_of_integrals_eq
-- name    : SymPolyOpt.Putinar.invariant_of_integrals_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:35.035222+00:00
-- url     : https://prove2.me/theorems/53010c67-6c5b-40fe-aa0b-d738c247dae6
-- title:
--   Theorem 3.2 proof, p. 11 — if ∫ h dμ = ∫ h^σ dμ for all h and all σ ∈ G, μ finite on compact K, then μ is G-invariant
-- statement:
--   Let $G$ be a finite subgroup of $\mathrm{GL}_n(\mathbb R)$, let $g_1,\dots,g_m\in\mathbb R[X]$ with $K=\{x:g_j(x)\ge0,\ j=1,\dots,m\}$ compact, and let $\mu$ be a finite Borel measure on $\mathbb R^n$ with $\mu(\mathbb R^n\setminus K)=0$. Suppose that
--   $$\int h\,d\mu=\int h^\sigma\,d\mu\qquad\text{for every }h\in\mathbb R[X]\text{ and every }\sigma\in G.$$
--   Then $\mu$ is $G$-invariant: $\mu^\sigma=\mu$ for all $\sigma\in G$.
--
--   This is the last step of the proof of Theorem 3.2: the measure produced by Putinar's theorem from a $G$-linear functional is automatically $G$-invariant, because a finite measure with compact support is determined by its polynomial moments.
--
--   **Formalization Note** $\mu^\sigma$ is the image of $\mu$ under $x\mapsto\sigma x$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 11, proof of Theorem 3.2, last display and the sentence after it

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

namespace SymPolyOpt.Putinar

open MeasureTheory MvPolynomial

theorem invariant_of_integrals_eq {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (g : Fin m → MvPolynomial (Fin n) ℝ) (hK : IsCompact (feasK g))
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (hμK : μ (feasK g)ᶜ = 0)
    (hint : ∀ σ ∈ G, ∀ h : MvPolynomial (Fin n) ℝ,
      ∫ x, eval x h ∂μ = ∫ x, eval x (polyAct σ h) ∂μ) :
    IsGInvariantMeasure G μ := by sorry

end SymPolyOpt.Putinar
