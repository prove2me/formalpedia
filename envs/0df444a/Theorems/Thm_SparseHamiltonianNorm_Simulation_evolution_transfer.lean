-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_evolution_transfer
-- name    : SparseHamiltonianNorm.Simulation.evolution_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:53.382394+00:00
-- url     : https://prove2.me/theorems/28b9b2c6-24fa-42c9-811d-9c551ea5a1a3
-- title:
--   Proposition 9 — Transfer identity, analyticity, contractivity, and boundary evolution
-- statement:
--   Let $d\ge1$, $\Lambda>0$, $t\ge0$, $M=M^\dagger$, and $V^\dagger V=I$ on finite complex spaces. The actual history resolvent is bijective for every $|z|<1$, and its transfer matrix satisfies
--   $$\Phi_t(z)=D+zC(I-zA)^{-1}B=\exp[-t\sqrt d\,\Lambda V^\dagger(I+zU_M)(I-zU_M)^{-1}V].$$
--   It is analytic and has operator norm at most one in that disk. The tangent and resolvent singularities in $[-\pi,\pi]$ form a finite set. Outside this set, radial limits are
--   $$\lim_{r\uparrow1}\Phi_t(re^{i\theta})=\exp(-itH_\theta),\quad H_\theta=\sqrt d\,\Lambda V^\dagger(2M-uI)(I+2uM)^{-1}V,\ u=\tan(\theta/2).$$
--   At phase zero the radial limit is $\exp(-itH)$ for $H=2\sqrt d\,\Lambda V^\dagger MV$. These conclusions identify the full transfer family rather than assuming a boundary inverse on the infinite history space.
--
--   Differences from the source:
--   - generalization: the sparse-entry lift M and public isometry V of Section 3 → any finite Hermitian M and any finite isometry V; reason: the source equations and feedback identity use only Hermiticity and isometry, so every source lift is included
--   - encoding: radial boundary values apart from finitely many phases → explicit one-sided limits and an explicitly defined exceptional set in the integration interval; reason: no inverse value at a singular phase is used to assert a boundary identity
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Proposition 9, p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=14; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Coupling

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
open Filter
open scoped Topology
/-- Li--Wang, Proposition 9, pp.14--15, all of Eqs. (42)--(45). -/
theorem evolution_transfer (n e d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (hd : 1 ≤ d) (hΛ : 0 < Λ) (ht : 0 ≤ t)
    (hV : V.conjTranspose * V = 1) (hM : M.IsHermitian) :
    (∀ z : ℂ, ‖z‖ < 1 → Function.Bijective (historyResolvent d Λ t V M z) ∧
      transfer d Λ t V M z = diskResponse d Λ t V M z ∧ opNorm (transfer d Λ t V M z) ≤ 1) ∧
    AnalyticOnNhd ℂ (transfer d Λ t V M) {z | ‖z‖ < 1} ∧
    {θ | exceptionalPhase M θ}.Finite ∧
    (∀ θ ∈ Set.Icc (-Real.pi) Real.pi, ¬ exceptionalPhase M θ →
      Tendsto (fun r : ℝ => transfer d Λ t V M ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[Set.Iio 1] 1) (𝓝 (evolution t (phaseH d Λ V M θ)))) ∧
    Tendsto (fun r : ℝ => transfer d Λ t V M (r : ℂ)) (𝓝[Set.Iio 1] 1)
      (𝓝 (evolution t (compressedH d Λ V M))) := by sorry
end SparseHamiltonianNorm.Simulation
