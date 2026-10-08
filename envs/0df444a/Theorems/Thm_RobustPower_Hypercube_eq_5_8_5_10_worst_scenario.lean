-- Prove2me | Theorems.Thm_RobustPower_Hypercube_eq_5_8_5_10_worst_scenario
-- name    : RobustPower.Hypercube.eq_5_8_5_10_worst_scenario
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:57.820613+00:00
-- url     : https://prove2.me/theorems/9c8b9fc9-fe23-43d9-bdbb-130960372f6e
-- title:
--   Eqs. (5.8)–(5.10) — on a hypercube the worst corner $\bar\omega$ is a scenario
-- statement:
--   Let $\Omega$ be a scenario set with data $A(\omega),B(\omega),b(\omega),d(\omega)$, and suppose the uncertainty set $\mathcal U=\{(A(\omega),B(\omega),b(\omega),d(\omega)):\omega\in\Omega\}$ is a hypercube. Then there is a scenario $\bar\omega\in\Omega$ whose data are entrywise the worst possible:
--
--   $$A_{ij}(\bar\omega)=\min_{\omega\in\Omega}A_{ij}(\omega),\quad B_{ij}(\bar\omega)=\min_{\omega\in\Omega}B_{ij}(\omega),\quad b_i(\bar\omega)=\max_{\omega\in\Omega}b_i(\omega),\quad d_j(\bar\omega)=\max_{\omega\in\Omega}d_j(\omega)$$
--
--   for all $i,j$; that is, $A(\bar\omega)\le A(\omega)$, $B(\bar\omega)\le B(\omega)$, $b(\omega)\le b(\bar\omega)$ and $d(\omega)\le d(\bar\omega)$ entrywise for every $\omega\in\Omega$.
--
--   This is where the hypercube assumption enters the proof of Theorem 5.4: for a general uncertainty set the entrywise extremes need not be realized by a single scenario.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 31–32, Eqs. (5.8)–(5.10) and the sentence following them

import Definitions.Def_RobustPower_Hypercube_DataBox

namespace RobustPower.Hypercube

/-- Equations (5.8)–(5.10) (pp. 31–32): if the uncertainty set is a hypercube, the
data `vec(Ā, B̄, b̄, d̄)` made of the entrywise minima of `A(ω)`, `B(ω)` and the
entrywise maxima of `b(ω)`, `d(ω)` over `ω ∈ Ω` is realized by a scenario `ω̄`. -/
theorem eq_5_8_5_10_worst_scenario
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hU : IsHypercube (uncertaintySet A B b d)) :
    ∃ ωbar : Ω,
      (∀ ω i j, A ωbar i j ≤ A ω i j) ∧
      (∀ ω i j, B ωbar i j ≤ B ω i j) ∧
      (∀ ω i, b ω i ≤ b ωbar i) ∧
      (∀ ω j, d ω j ≤ d ωbar j) := by sorry

end RobustPower.Hypercube
