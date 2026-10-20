-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem16
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem16
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:45:36.890449+00:00
-- url     : https://prove2.me/theorems/a93792a8-6a29-491b-9f75-b427a4fa62ae
-- title:
--   Theorem 16 (Structure of infinitesimal divisible channels)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Let $\mathcal I$ be the channels admitting exact finite CPTP products with all factors within every prescribed positive tolerance of the identity. Let $\mathcal I^{\prime}$ impose in addition that every factor is Markovian, meaning a member of a continuous CPTP one-parameter semigroup. Let $\mathcal J$ consist of endpoints of continuous two-parameter CPTP evolutions with the composition law and local identity limit. Then
--
--   $$\overline{\mathcal I}=\overline{\mathcal I^{\prime}}=\overline{\mathcal J}.$$
--
--   In particular, every $T\in\overline{\mathcal I}$ and every $\varepsilon>0$ admit a finite product of Markovian channels $M_1\cdots M_m$ with $\|T-M_1\cdots M_m\|<\varepsilon$.
--
--   This is the paper’s general-dimension representation result; it requires no differentiable generator for the evolutions in $\mathcal J$.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 14, Theorem 16 (Structure of infinitesimal divisible channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 16, PDF pp.13--15: all three bars are essential; the seed ID refers to this theorem. -/
theorem theorem16 {d : ℕ} (hd : 0 < d) :
    closure (fineProducts d true false) = closure (fineProducts d true true) ∧
    closure (fineProducts d true true) = closure (evolutionEndpoints d) ∧
    (∀ T : Super d, Infinitesimal true T → ∀ eps : ℝ, 0 < eps →
      ∃ factors : List (Super d), (∀ A ∈ factors, Markovian A) ∧ hsOperatorNorm (T - factors.prod) < eps) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
