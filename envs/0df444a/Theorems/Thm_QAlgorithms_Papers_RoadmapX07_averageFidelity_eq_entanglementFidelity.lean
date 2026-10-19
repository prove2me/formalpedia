-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapX07_averageFidelity_eq_entanglementFidelity
-- name    : QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:14.842123+00:00
-- url     : https://prove2.me/theorems/4b0c172c-fcae-4496-9353-c413f9a52bc6
-- title:
--   Average channel fidelity and entanglement fidelity
-- statement:
--   Let $d$ be a positive integer and let $\mathcal E$ be a trace-preserving quantum operation on a $d$-dimensional quantum system $Q$. Define its average fidelity by $\overline F(\mathcal E)=\int \langle\psi|\mathcal E(|\psi\rangle\langle\psi|)|\psi\rangle\,d\psi$, where $d\psi$ is the uniform Haar probability measure on normalized pure states. Let $R$ be a $d$-dimensional reference system, let $|\phi_d\rangle=d^{-1/2}\sum_{j=0}^{d-1}|j\rangle_R|j\rangle_Q$, and define $F_e(\mathcal E)=\langle\phi_d|(\mathrm{id}_R\otimes\mathcal E)(|\phi_d\rangle\langle\phi_d|)|\phi_d\rangle$. Then
--
--   $$
--   \overline F(\mathcal E)=\frac{d F_e(\mathcal E)+1}{d+1}.
--   $$
--
--   This identity converts entanglement fidelity into the average probability of preserving a uniformly distributed pure state.
--
--   **Formalization Note** The frozen channel predicate supplies complete positivity, trace preservation and linearity through a normalized Kraus representation. The Haar state measure is the image of normalized full-unitary Haar measure applied to a fixed unit vector; channel integrability is established in the imported definition module. Entanglement fidelity is an overlap probability, independent of the choice of maximally entangled state.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Equation (3); proof on PDF pages 1–2, PDF p. 1. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapX07

/-- Nielsen, arXiv:quant-ph/0205035v2, Equation (3), PDF p. 1; proof on pp. 1-2.
For a trace-preserving quantum operation on a finite positive-dimensional system,
the normalized Haar average of the pure-state overlap equals
`(d * F_e + 1) / (d + 1)`. Entanglement fidelity uses the normalized maximally
entangled state on reference and system, with the channel acting on the system alone.
The imported channel-fidelity definitions establish Haar normalization and integrability. -/
theorem averageFidelity_eq_entanglementFidelity (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    QuditFidelity.averageFidelity d hd E =
      ((d : ℝ) * QuditFidelity.entanglementFidelity d hd E + 1) / ((d : ℝ) + 1) := by sorry

end QAlgorithms.Papers.RoadmapX07
