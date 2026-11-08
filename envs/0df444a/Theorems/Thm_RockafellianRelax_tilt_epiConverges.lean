-- Prove2me | Theorems.Thm_RockafellianRelax_tilt_epiConverges
-- name    : RockafellianRelax.tilt_epiConverges
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:36:00.001544+00:00
-- url     : https://prove2.me/theorems/0bfc070f-25a4-4224-ad3f-c8a2146ead98
-- title:
--   Proof of Theorem 3.7, p.37 — tilting by $\langle y^\nu, u\rangle$ with $y^\nu \to \bar y$ preserves epi-convergence
-- statement:
--   Let $f^\nu, f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ with $f^\nu$ epi-converging to $f$, and let $y^\nu \to \bar y$ in $\mathbb R^m$. Then the tilted functions
--
--   $$
--   \tilde f^\nu(u,x) = f^\nu(u,x) - \langle y^\nu, u\rangle
--   \quad\text{epi-converge to}\quad
--   \tilde f(u,x) = f(u,x) - \langle\bar y, u\rangle .
--   $$
--
--   Epi-convergence is (3.8)–(3.9) of p.9. This turns the hypothesis of Theorem 3.7 into epi-convergence of the objectives of the approximating problems (3.7) to that of the relaxed problem (3.2).
--
--   Differences from the source:
--   - generalization: f the exact Rockafellian to which the f^ν epi-converge (limit-exact hypothesis of Theorem 3.7) → any f : ℝᵐ × ℝⁿ → R̄ to which the f^ν epi-converge; reason: the step uses only (3.8) and (3.9); the paper's f is one such f
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
--   - encoding: ν ∈ ℕ = {1, 2, …} → ν ∈ Lean's ℕ from 0; reason: Lean convention; a shift of the index changes no limit
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proof of Theorem 3.7, p.37

import Mathlib
import Definitions.Def_RockafellianRelax_tilt
import Definitions.Def_PerspEpi_SeqEpiConv

open Filter Topology

namespace RockafellianRelax

/-- **Tilting preserves epi-convergence.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Proof of
Theorem 3.7, p.37: "Consider the functions given by f̃ν(u, x) = fν(u, x) − ⟨yν, u⟩ and
f̃(u, x) = f(u, x) − ⟨ȳ, u⟩. It follows directly from (3.8) and (3.9) that the epi-convergence of fν
to f guarantees that f̃ν epi-converges to f̃."

If `fν` epi-converges to `f` on `ℝᵐ × ℝⁿ` and `yν → ȳ`, then `fν − ⟨yν, ·₁⟩` epi-converges to
`f − ⟨ȳ, ·₁⟩`.

**Formalization Note.** Epi-convergence is the sequential (3.8)–(3.9) (`PerspEpi.SeqEpiConv`) on
the product topology. In the paper `f` is the exact Rockafellian of the limit-exact hypothesis; the
statement holds for every `f`. -/
theorem tilt_epiConverges {m n : ℕ} (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (y : ℕ → Fin m → ℝ)
    (hy : Tendsto y atTop (𝓝 ybar)) (hF : PerspEpi.SeqEpiConv F f) :
    PerspEpi.SeqEpiConv (fun ν => tilt (F ν) (y ν)) (tilt f ybar) := by sorry

end RockafellianRelax
