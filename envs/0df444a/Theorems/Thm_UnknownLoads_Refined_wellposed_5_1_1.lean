-- Prove2me | Theorems.Thm_UnknownLoads_Refined_wellposed_5_1_1
-- name    : UnknownLoads.Refined.wellposed_5_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:07.570848+00:00
-- url     : https://prove2.me/theorems/458de6ba-785f-4007-8916-123d0d227994
-- title:
--   §5.1.1 — almost surely, (9a)–(9b) have unique càdlàg solutions for every n
-- statement:
--   Consider the coupled construction of §5.1.1 with control parameters $\alpha_n\in(0,1)$. Then there is a set $\Gamma_0$ of probability one such that, for each $\omega\in\Gamma_0$ and each $n\ge1$, there exist unique càdlàg functions $q_n(\omega):[0,T]\to Q$ and $\ell_n(\omega):[0,T]\to\mathbb N$ solving
--   $$
--   q_n(t)=q_n(0)+\mathcal A_n(q_n,\ell_n,t)-\mathcal D_n(q_n,t),\qquad \ell_n(t)=\ell_n(0)+\sum_{k=1}^{\mathcal N^\lambda_n(t)}\Delta\big[\mathbb 1_{\{\cdots\}}-\mathbb 1_{\{\cdots\}}\big]
--   $$
--   for all $t\in[0,T]$ (equations (9a)–(9b)).
--
--   This is the well-posedness of the construction: it guarantees that the system of processes in all other statements exists and is pinned down almost surely by the equations.
--
--   **Formalization Note** Uniqueness is equality on $[0,T]$ with every other solution; values outside $[0,T]$ are not constrained by the equations.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 24, §5.1.1 (unnumbered well-posedness claim)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem wellposed_5_1_1 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (prim : Primitives D Ω P) (α : ℕ → ℝ) (hα : ∀ n : ℕ, 1 ≤ n → α n ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n →
      ∃ q : ℝ → ℕ → ℝ, ∃ ℓ : ℝ → ℕ, prim.Solves (α n) n ω q ℓ ∧
        ∀ (q' : ℝ → ℕ → ℝ) (ℓ' : ℝ → ℕ), prim.Solves (α n) n ω q' ℓ' →
          ∀ t ∈ Icc 0 D.T, q' t = q t ∧ ℓ' t = ℓ t := by sorry

end UnknownLoads.Refined
