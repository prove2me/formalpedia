-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_convex_comb_strictly_feasible
-- name    : TVSDP.PolyOpt.convex_comb_strictly_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:01.338992+00:00
-- url     : https://prove2.me/theorems/4a9490d0-49ef-47de-a706-b538b033dfb6
-- title:
--   Proof of Theorem 4, p. 13 — $(1-\lambda)x^\varepsilon+\lambda x^s$ is strictly feasible and its objective tends to $\langle c,x^\varepsilon\rangle$ as $\lambda\to0$
-- statement:
--   Consider a TV-SDP with polynomial data and operator $\mathcal F$. Let $x$ be a feasible solution, and let $x^s\in\mathbf L^n$ and $\varepsilon>0$ satisfy $\mathcal Fx^s(t)\succeq\varepsilon I$ for almost every $t\in[0,1]$. For $\lambda\in(0,1)$ put $x^{\lambda}=(1-\lambda)x+\lambda x^s$. Then:
--
--   1. for every $\lambda\in(0,1)$, $x^\lambda\in\mathbf L^n$ and
--   $$\mathcal Fx^{\lambda}(t)\succeq \lambda\varepsilon\, I\quad\text{for almost every } t\in[0,1],$$
--   so $x^\lambda$ is strictly feasible;
--   2. $\langle c,x^{\lambda}\rangle_{\mathbf L^n}\to\langle c,x\rangle_{\mathbf L^n}$ as $\lambda\to0^+$.
--
--   This is the first step of the proof of Theorem 4: a feasible solution is perturbed into a strictly feasible one with almost the same objective value.
--
--   **Formalization Note** The page says only that $x^{\lambda,\varepsilon}$ "is also strictly feasible"; the explicit margin $\lambda\varepsilon$ is the one that strict feasibility of the combination yields, and stating it makes the result slightly stronger. The limit is one-sided, $\lambda\to0$ within $(0,\infty)$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 13, proof of Theorem 4, second paragraph

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Setting

namespace TVSDP.PolyOpt

open MeasureTheory Filter Topology

/-- Proof of Theorem 4, p. 13: if `x` is feasible and `xs ∈ L^n` satisfies `𝓕xs(t) ⪰ εI` a.e. on
`[0,1]`, then for every `λ ∈ (0,1)` the combination `(1-λ)x + λxs` lies in `L^n` and satisfies
`𝓕((1-λ)x + λxs)(t) ⪰ λεI` a.e. on `[0,1]` (so it is strictly feasible), and its objective value
tends to that of `x` as `λ → 0⁺`. -/
theorem convex_comb_strictly_feasible {n m : ℕ} (P : Data n m) (x xs : ℝ → Fin n → ℝ)
    (hx : Feasible P x) (hxs : xs ∈ Ln n) (ε : ℝ) (hε : 0 < ε)
    (hxsε : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      (F P xs t - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) :
    (∀ lam ∈ Set.Ioo (0:ℝ) 1,
      (1 - lam) • x + lam • xs ∈ Ln n ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
        (F P ((1 - lam) • x + lam • xs) t
          - (lam * ε) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) ∧
    Tendsto (fun lam : ℝ => obj P ((1 - lam) • x + lam • xs)) (𝓝[>] 0) (𝓝 (obj P x)) := by sorry

end TVSDP.PolyOpt
