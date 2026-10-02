-- Prove2me | Theorems.Thm_TeschlQM_Atomic_hvz
-- name    : TeschlQM.Atomic.hvz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:15:54.700828+00:00
-- url     : https://prove2.me/theorems/7ab9d8bf-f270-4eae-af12-6e05f7e5fc49
-- title:
--   Theorem 11.2 (HVZ) — σ_ess(H^(N)) = [λ^(N−1), ∞)
-- statement:
--   Let $\gamma_{ne}, \gamma_{ee} > 0$ and let $H^{(N)}$ be the self-adjoint atomic Hamiltonian
--   $$H^{(N)} = -\sum_{j=1}^N \Delta_j - \sum_{j=1}^N \frac{\gamma_{ne}}{|x_j|} + \sum_{1 \le j < k \le N} \frac{\gamma_{ee}}{|x_j - x_k|}, \qquad \mathfrak D(H^{(N)}) = H^2(\mathbb R^{3N}).$$
--   Then $H^{(N)}$ is bounded from below and
--   $$\sigma_{ess}(H^{(N)}) = [\lambda^{N-1}, \infty), \qquad \text{where } \lambda^{N-1} = \min \sigma(H^{(N-1)}) < 0,$$
--   $H^{(N-1)}$ being the Hamiltonian of the same atom with $N - 1$ electrons (same $\gamma_{ne}, \gamma_{ee}$).
--
--   The theorem (Hunziker, van Winter, Zhislin) locates the essential spectrum of an atom: it starts at the ground state energy of the ion with one electron removed, so everything below $\lambda^{N-1}$ is discrete spectrum.
--
--   **Formalization Note.** $H^{(N)}$ is `atomicHamiltonian γne γee N` on `Lp ℂ 2` over `EuclideanSpace ℝ (Fin N × Fin 3)`: the `LinearPMap` sum of the Fourier-defined $H_0 = -\Delta$ on $H^2$ and the multiplication operator by $V^{(N)}$. The spectrum and essential spectrum are the ones defined from the resolvent (`spectrum`, `essentialSpectrum`), not Mathlib's Banach-algebra spectrum. "$\lambda^{N-1} = \min\sigma(H^{(N-1)})$" is stated as $\lambda^{N-1} \in \sigma(H^{(N-1)})$ and every $z \in \sigma(H^{(N-1)})$ is real with $\lambda^{N-1} \le z$; $\lambda^{N-1}$ is thus defined from the $(N-1)$-electron operator, independently of $H^{(N)}$, and its attainment (min, not inf) and negativity are both claimed. $[\lambda^{N-1}, \infty)$ is the image of `Set.Ici λ` in $\mathbb C$. The theorem is stated for $N \ge 1$. For $N = 1$ the "ion" $H^{(0)}$ has no electrons: it is the zero operator on $L^2(\mathbb R^0) \cong \mathbb C$, so $\lambda^0 = 0$ and the page's claim $\lambda^{N-1} < 0$ is false there; negativity is claimed for $N \ge 2$ only, while $\sigma_{ess}(H^{(1)}) = [0, \infty)$ is kept.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 242, Theorem 11.2

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

/-- Teschl, Theorem 11.2 (HVZ), p. 242. Let `H^{(N)}` be the atomic Hamiltonian (11.6) with
`γ_ne, γ_ee > 0` (11.7). Then `H^{(N)}` is bounded from below and
`σ_ess(H^{(N)}) = [λ^{N-1}, ∞)` (11.9), where `λ^{N-1} = min σ(H^{(N-1)}) < 0` is the minimum of
the spectrum of the `(N-1)`-electron Hamiltonian with the same `γ_ne, γ_ee`.
"`λ^{N-1} = min σ(H^{(N-1)})`" is stated as: `λ^{N-1} ∈ σ(H^{(N-1)})` and every `z ∈ σ(H^{(N-1)})`
is real with `λ^{N-1} ≤ z`. The theorem is stated for `N ≥ 1`. For `N = 1` the ion `H^{(0)}` has no
electrons: it is the zero operator on `L²(ℝ⁰) ≅ ℂ`, so `λ⁰ = 0`, and the page's claim `λ^{N-1} < 0`
is false there. The negativity is therefore claimed for `N ≥ 2` only (the book's slip, corrected);
`σ_ess(H^{(1)}) = [0, ∞)` is kept. -/
theorem hvz (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) (hN : 1 ≤ N) :
    (∃ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee N) γ) ∧
      ∃ lam : ℝ, ((lam : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)) ∧
          ∀ z ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)), z.im = 0 ∧ lam ≤ z.re) ∧
        (2 ≤ N → lam < 0) ∧
        TeschlQM.Shared.essentialSpectrum (atomicHamiltonian γne γee N) =
          (fun t : ℝ => (t : ℂ)) '' Set.Ici lam := by sorry

end TeschlQM.Atomic
