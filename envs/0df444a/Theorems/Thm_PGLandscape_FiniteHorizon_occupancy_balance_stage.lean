-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_occupancy_balance_stage
-- name    : PGLandscape.FiniteHorizon.occupancy_balance_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:15.46398+00:00
-- url     : https://prove2.me/theorems/80acc25d-ac26-4ed5-b767-9d7a9c7dc015
-- title:
--   App. D.2, proof of Theorem 3, p. 41 — stage-wise balance: η_π(ℳ) = (1 − γ)ρ(ℳ) + γ ∫_{S_h} P(ℳ|s, π(s)) η_π(ds) for ℳ ⊆ S_{h+1}, h < H
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process whose states are split into stages $\mathcal S_1,\dots,\mathcal S_{H+1}$ as in Condition 3: from $\mathcal S_h$, $h\le H$, every feasible action leads to $\mathcal S_{h+1}$ with probability one, and $\mathcal S_{H+1}=\{\tau\}$ is a costless absorbing state. Let $\pi\in\Pi$ be a feasible measurable stationary policy and $\eta_\pi$ its discounted state-occupancy measure. Then for every stage $h$ with $1\le h<H$ and every measurable $\mathcal M\subseteq\mathcal S_{h+1}$,
--   $$\eta_\pi(\mathcal M)=(1-\gamma)\rho(\mathcal M)+\gamma\int_{\mathcal S_h}P(\mathcal M\mid s,\pi(s))\,\eta_\pi(ds).$$
--
--   The identity says that the occupancy of stage $h+1$ is fed only by restarts and by the previous stage; it is how the backward induction in the proof of Theorem 3 transports almost-sure statements from stage $h+1$ back to stage $h$.
--
--   **Formalization Note** The page states the identity for every $h\in\{1,\dots,H\}$. At $h=H$ it fails in general: $\mathcal S_{H+1}=\{\tau\}$ is absorbing, so $\tau$ also feeds itself and the general balance equation (Lemma 17) gives $\eta_\pi(\{\tau\})=(1-\gamma)\rho(\{\tau\})+\gamma\int_{\mathcal S_H}P(\{\tau\}\mid s,\pi(s))\,\eta_\pi(ds)+\gamma\,\eta_\pi(\{\tau\})$; the page's justification "$P(\mathcal S_{h+1}\mid s,\pi(s))=0$ for $s\notin\mathcal S_h$" is false for $h=H$, $s=\tau$. The proof of Theorem 3 uses the case $h=H$ only with an integrand vanishing on $\mathcal S_{H+1}$, so nothing downstream is lost; the statement is restricted to $h<H$. Integrals are Lebesgue integrals in $[0,\infty]$; $\mathcal M$ is measurable.
-- source:
--   arXiv:1906.01786v3, App. D.2, proof of Theorem 3, balance equation after inequality (a), p. 41

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions
import Definitions.Def_PGLandscape_FiniteHorizon_Stages

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- The stage-wise balance equation, arXiv:1906.01786v3, App. D.2, proof of Theorem 3, p. 41: under
the stage structure of Condition 3, for every feasible measurable policy `π ∈ Π`, every stage
`h ∈ {1, …, H − 1}` and every measurable `M ⊆ S_{h+1}`,
`η_π(M) = (1 − γ) ρ(M) + γ ∫_{S_h} P(M | s, π(s)) η_π(ds)`.
The page states it for `h ∈ {1, …, H}`; at `h = H`, `M = S_{H+1} = {τ}` it fails (the absorbing
state also feeds itself), so the statement is restricted to `h < H`. -/
theorem occupancy_balance_stage {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (H : ℕ) (stage : S → ℕ) (τ : S) (hst : IsStaged M H stage τ)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) (h : ℕ) (h1 : 1 ≤ h) (hH : h < H)
    (B : Set S) (hB : MeasurableSet B) (hBS : B ⊆ {s | stage s = h + 1}) :
    PGLandscape.Closure.occupancy M π B = ENNReal.ofReal (1 - M.γ) * M.ρ B +
      ENNReal.ofReal M.γ * ∫⁻ s in {s | stage s = h}, PGLandscape.Closure.stepKernel M π s B ∂(PGLandscape.Closure.occupancy M π) := by sorry

end PGLandscape.FiniteHorizon
