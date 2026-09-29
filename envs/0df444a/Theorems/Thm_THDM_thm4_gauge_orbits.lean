-- Prove2me | Theorems.Thm_THDM_thm4_gauge_orbits
-- name    : THDM.thm4_gauge_orbits
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:07:03.256993+00:00
-- url     : https://prove2.me/theorems/d0d7a8d8-b5a4-479f-91f3-60a8cc17a17a
-- title:
--   Theorem 4: Higgs fields with the same $K$ are gauge equivalent, and the orbits fill the forward light cone
-- statement:
--   **Theorem 4 of arXiv:hep-ph/0605184.** Any two Higgs-doublet field configurations giving the same matrix $K$ of gauge-invariant scalar products are related by a gauge transformation, and the space of gauge orbits is parametrised by the four-vectors $(K_0,K)$ lying on or inside the forward light cone.
--
--   Concretely, three assertions are combined. First, if $\phi\phi^\dagger=\phi'\phi'^\dagger$ then there is a unitary $U$ with $\phi'=\phi U^{\mathsf T}$. Second, the invariants of any configuration satisfy $K_0\ge0$ and $|K|^2\le K_0^2$ (3.19). Third, every pair $(K_0,K)$ with $K_0\ge0$ and $|K|^2\le K_0^2$ is realised by some configuration. Together these say that the map $\phi\mapsto(K_0,K)$ is onto the closed forward light cone and its fibres are exactly the gauge orbits, which is what licenses the whole gauge-invariant treatment of the potential.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Appendix A, p. 18, Theorem 4 (with eqs. A7-A21 and 3.19)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem thm4_gauge_orbits :
    (∀ φ φ' : HiggsMat, Kmat φ = Kmat φ' → GaugeEquiv φ φ') ∧
    (∀ φ : HiggsMat, (K0 φ, Kvec φ) ∈ forwardCone) ∧
    (∀ p : ℝ × (Fin 3 → ℝ), p ∈ forwardCone →
        ∃ φ : HiggsMat, K0 φ = p.1 ∧ Kvec φ = p.2) := by sorry

end THDM
