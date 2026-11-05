-- Prove2me | Theorems.Thm_Viterbo_Cap_galerkin_cerami
-- name    : Viterbo.Cap.galerkin_cerami
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T17:50:28.390343+00:00
-- url     : https://prove2.me/theorems/d4af98c1-7114-429b-a7e6-db506ab85dad
-- title:
--   Uniform Cerami bound for the Galerkin action functionals of a Hamiltonian with homogeneous asymptotics and negative ½⟨∇H,z⟩ − H at infinity
-- statement:
--   Let $\kappa$ be a finite type and $H:\mathbb C^\kappa\to\mathbb R$ satisfy `Viterbo.Cap.EngineHyp H V C R γ₀` ($H$ smooth, $\|\nabla H(z)\|\le C(1+\|z\|)$, $r^{-1}\nabla H(rz)\to V(z)$ uniformly on bounded sets as $r\to\infty$ for a continuous $V$ with $\|V(z)\|\le C\|z\|$, and $\tfrac12\langle\nabla H(z),z\rangle-H(z)\le-\gamma_0<0$ for $\|z\|\ge R$). Let $a_0>0$. Then there are $N_0$, $R_1$ and $c_1>0$ such that for every $N\ge N_0$ and every Galerkin coefficient vector $x$ on the frequencies `frequency N` ($0,-1,\dots,-N$ and $1,\dots,N+1$) with $\Phi_N(x)\ge a_0$ and $\|x\|\ge R_1$, where $\Phi_N$ = `OAI.FourierPolynomial.action (frequency N) H`, one has $c_1\le(1+\|x\|)\,\|\nabla\Phi_N(x)\|$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, a step in the proof of the capacity statement (Hofer–Zehnder argument, Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3)

import Mathlib
import Definitions.Def_ViterboCap

open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

namespace Viterbo.Cap

theorem galerkin_cerami {κ : Type} [Fintype κ] [DecidableEq κ] {H : Vector κ → ℝ} {V : Vector κ → Vector κ} {C R γ₀ : ℝ}
    (hE : EngineHyp H V C R γ₀) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ N₀ : ℕ, ∃ R₁ c₁ : ℝ, 0 < c₁ ∧ ∀ N, N₀ ≤ N →
      ∀ x : Coeff (Fin (N + 1) ⊕ Fin (N + 1)) κ, a₀ ≤ FourierPolynomial.action (frequency N) H x → R₁ ≤ ‖x‖ →
        c₁ ≤ (1 + ‖x‖) * ‖gradient (FourierPolynomial.action (frequency N) H) x‖ := by
  sorry

end Viterbo.Cap
