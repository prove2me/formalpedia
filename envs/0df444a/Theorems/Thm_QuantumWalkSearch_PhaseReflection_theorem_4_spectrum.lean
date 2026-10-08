-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_theorem_4_spectrum
-- name    : QuantumWalkSearch.PhaseReflection.theorem_4_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:46:06.2227+00:00
-- url     : https://prove2.me/theorems/e2bf81bf-bc0b-4b03-bac8-aa463cdcb4ba
-- title:
--   Theorem 4 (consequences used for Theorem 6) — eigenvalues of $W(P)$ on $\mathcal A+\mathcal B$ are $\pm1$ or $e^{\pm2i\theta}$, and its fixed vectors there form $\mathcal A\cap\mathcal B$
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite set $X$ with stationary distribution $\pi$, $W(P)$ its quantum walk on $\mathcal H=\mathbb C^{X\times X}$ and $D(P)$ its discriminant matrix. Then:
--
--   1. $W(P)$ maps $\mathcal A+\mathcal B$ into itself.
--   2. If $v\in\mathcal A+\mathcal B$, $v\neq0$, and $W(P)v=\mu v$, then
--   $$\mu=1,\quad \mu=-1,\quad\text{or}\quad \mu=e^{\pm2i\theta}\ \text{ with }\theta\in(0,\tfrac{\pi}{2})\text{ and }\cos\theta\text{ a singular value of }D(P).$$
--   3. A vector $v$ satisfies $v\in\mathcal A+\mathcal B$ and $W(P)v=v$ if and only if $v\in\mathcal A\cap\mathcal B$.
--
--   These are the parts of Szegedy's Theorem 4 that the proof of Theorem 6 uses: they say that phase estimation on $W(P)$ only ever sees the phases $0$, $\pi$ and $\pm2\theta$, and that the phase $0$ is carried by $\mathcal A\cap\mathcal B$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 7, Theorem 4 (Szegedy [29]), parts 1–4 (the direction used in the proof of Theorem 6, p. 9)

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_Walk

namespace QuantumWalkSearch.PhaseReflection

/-- The consequences of Theorem 4 (p. 7) used in the proof of Theorem 6, for an irreducible
chain: `W(P)` maps `A + B` into itself; every eigenvalue of `W(P)` with an eigenvector in `A + B`
is `1`, `−1`, or `e^{±2iθ}` with `θ ∈ (0, π/2)` and `cos θ` a singular value of `D(P)`; and the
`1`-eigenvectors of `W(P)` in `A + B` are exactly the vectors of `A ∩ B`. -/
theorem theorem_4_spectrum {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ)
    (πd : X → ℝ) (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDist P πd) :
    (∀ v ∈ spaceA P ⊔ spaceB P πd, walk P πd v ∈ spaceA P ⊔ spaceB P πd) ∧
    (∀ (μ : ℂ), ∀ v ∈ spaceA P ⊔ spaceB P πd, v ≠ 0 → walk P πd v = μ • v →
      μ = 1 ∨ μ = -1 ∨ ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), IsSingularValue P πd (Real.cos θ) ∧
        (μ = Complex.exp (2 * (θ : ℂ) * Complex.I) ∨
          μ = Complex.exp (-(2 * (θ : ℂ) * Complex.I)))) ∧
    (∀ v, (v ∈ spaceA P ⊔ spaceB P πd ∧ walk P πd v = v) ↔ v ∈ spaceA P ⊓ spaceB P πd) := by sorry

end QuantumWalkSearch.PhaseReflection
