-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_iteration_converges
-- name    : SLQSolv.UnifConvex.iteration_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:50.570333+00:00
-- url     : https://prove2.me/theorems/5f7b8b22-5d29-46e5-9420-da14e0f30d90
-- title:
--   Proof of Theorem 4.5, p. 2290 — the Riccati iterates converge uniformly to a solution of (4.6) with R + DᵀPD ≥ λI
-- statement:
--   Assume (H1)–(H2), (4.2) with constant $\lambda>0$ and (4.1) with constant $\alpha$, and let $\{P_i\}$ be the iteration (4.18)–(4.19) (see the item `iteration_monotone`). Then $\{P_i\}$ converges uniformly on $[0,T]$ to a limit $P$, and
--
--   $$R(s)+D(s)^\top P(s)D(s)=\lim_{i\to\infty}R(s)+D(s)^\top P_i(s)D(s)\ \ge\ \lambda I\quad\text{a.e. }s\in[0,T],$$
--
--   and $P$ solves the Riccati equation (4.6). Hence $P$ is a strongly regular solution of (4.6), with the constant $\lambda$ of (4.2).
--
--   This is the conclusion of the implication (i) ⇒ (ii) of Theorem 4.5.
--
--   **Formalization Note** Uniform convergence is `TendstoUniformlyOn` on $[0,T]$ for the entrywise (sup) norm on matrices, equivalent to convergence in $C([0,T];\mathbb S^n)$. The Riccati equation is in integral form, with the pseudoinverse; on the limit it is the inverse.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §4, proof of Theorem 4.5, p. 2290

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Iteration

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- §4, proof of Theorem 4.5, p. 2290. With the iteration (4.18)–(4.19) as in
`iteration_monotone`, the sequence `{Pᵢ}` converges uniformly on `[0, T]` to a limit `P`, which
solves the Riccati equation (4.6) and satisfies `R + DᵀPD ≥ λI` a.e. on `[0, T]`. -/
theorem iteration_converges {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω)
    (d : Data Ω n m) (h1 : H1 Bs d) (h2 : H2 Bs d)
    (lam : ℝ) (hlam : 0 < lam) (h42 : ∀ u, Adm Bs d 0 u → lam * sqNorm Bs d 0 u ≤ J0 Bs d 0 0 u)
    (α : ℝ) (h41 : ∀ t ≤ d.T, ∀ x : Fin n → ℝ, ((α * (x ⬝ᵥ x) : ℝ) : EReal) ≤ V0 Bs d t x)
    (Pseq : ℕ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP0 : IsLyapunovSol d 0 (Pseq 0))
    (hPsucc : ∀ i, IsLyapunovSol d (thetaOf d (Pseq i)) (Pseq (i + 1))) :
    ∃ P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ,
      TendstoUniformlyOn Pseq P atTop (Icc 0 d.T) ∧ IsRiccatiSol d P ∧
        ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) d.T)),
          (sigmaR d P s.toNNReal - lam • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by sorry

end SLQSolv.UnifConvex
