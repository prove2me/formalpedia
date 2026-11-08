-- Prove2me | Theorems.Thm_SmoothNestedSim_eq_EC_6_2
-- name    : SmoothNestedSim.eq_EC_6_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:39:13.655338+00:00
-- url     : https://prove2.me/theorems/aab149c8-47cf-4315-bf75-7c3913cfa3c2
-- title:
--   (EC.6.2): $|f(\mathbf x)|\le\|f\|_{\mathcal N_\Psi(\Omega)}\Psi(0)$ on $\Omega$
-- statement:
--   Let $\nu>0$, $\ell>0$, $\Omega\subseteq\mathbb R^d$ bounded and convex, and $f\in\mathcal N_\Psi(\Omega)$. Then for every $\mathbf x\in\Omega$,
--
--   $$
--   |f(\mathbf x)|\le\|f\|_{\mathcal N_\Psi(\Omega)}\,\Psi(0).
--   $$
--
--   The paper derives this from the reproducing property and Cauchy–Schwarz; it shows that $f$, and hence $\eta\circ f$, is bounded on $\Omega$, which makes the Monte Carlo term of the error a sum of bounded variables.
--
--   Differences from the source:
--   - reading: the chain |f(x)| = |⟨f, Ψ(x − ·)⟩| ≤ ‖f‖‖Ψ(x − ·)‖ = ‖f‖Ψ(x − x) = ‖f‖Ψ(0) → its outer inequality |f(x)| ≤ ‖f‖ Ψ(0); reason: the intermediate terms are the derivation; the outer inequality is what (EC.6.3) uses
--   - encoding: N_Ψ(Ω) is the closure of span{Ψ(· − x) : x ∈ Ω} under the N⁰ inner product (p.11) → f ∈ N_Ψ(Ω) iff some C ≥ 0 has (Σ cᵢ f(xᵢ))² ≤ C Σᵢⱼ cᵢcⱼ Ψ(xᵢ − xⱼ) for all finite families in Ω, and ‖f‖² is the least such C; reason: Aronszajn's criterion (Paulsen–Raghupathi 2016, Thm 3.11) identifies the two for a positive definite kernel, which the Matérn kernel is
--   - encoding: Ψ(x) by formula (3), which reads 0·∞ at x = 0 → Ψ(0) := 1; reason: 1 is the continuous extension of (3) at 0 (the ν = 1/2, 3/2 forms on p.11 give 1) and (EC.6.2) uses Ψ(0) as Ψ(x − x)
--   - generalization: x ∈ ℝ^d for a dimension d ≥ 1 → any d : ℕ, including d = 0; reason: ℝ⁰ is a single point and every claim stays true there; for d ≥ 1 the statement is the source's
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, proof of Theorem 1, (EC.6.2), p.ec13 (PDF p.59)

import Mathlib
import Definitions.Def_SmoothNestedSim_matern
import Definitions.Def_SmoothNestedSim_maternKernel
import Definitions.Def_SmoothNestedSim_RKHS
import Definitions.Def_SmoothNestedSim_rkhsNorm

namespace SmoothNestedSim

/-- **(EC.6.2): sup-norm bound by the RKHS norm** (Wang, Wang, Zhang, *Smooth Nested
Simulation*, arXiv:2201.02958v6, proof of Theorem 1, (EC.6.2), p.ec13 = PDF p.59): "The
reproducing property of RKHSs implies that for any `x ∈ Ω`,
`|f(x)| = |⟨f, Ψ(x − ·)⟩_{N_Ψ(Ω)}| ≤ ‖f‖_{N_Ψ(Ω)}‖Ψ(x − ·)‖_{N_Ψ(Ω)} = ‖f‖_{N_Ψ(Ω)}Ψ(x − x) = ‖f‖_{N_Ψ(Ω)}Ψ(0)`".

For `ν, ℓ > 0`, a bounded convex `Ω` and `f ∈ N_Ψ(Ω)`: `|f(x)| ≤ ‖f‖_{N_Ψ(Ω)} Ψ(0)` for all
`x ∈ Ω`. Only the outer inequality of the printed chain is stated. -/
theorem eq_EC_6_2 {d : ℕ} (ν ℓ : ℝ) (hν : 0 < ν) (hℓ : 0 < ℓ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩb : Bornology.IsBounded Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : f ∈ RKHS (maternKernel ν ℓ) Ω) :
    ∀ x ∈ Ω, |f x| ≤ rkhsNorm (maternKernel ν ℓ) Ω f * matern ν ℓ (0 : EuclideanSpace ℝ (Fin d)) := by sorry

end SmoothNestedSim
