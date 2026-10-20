-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P29_minimumFidelity_implies_minimumEntanglementFidelity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P29.minimumFidelity_implies_minimumEntanglementFidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:30:43.271643+00:00
-- url     : https://prove2.me/theorems/30611921-92ef-446f-a2f0-0f56fc0e9d8e
-- title:
--   Minimum fidelity implies minimum entanglement fidelity
-- statement:
--   Let $\mathcal H$ be a nonzero finite-dimensional complex Hilbert space, let $\mathcal H_0$ be an isomorphic reference space, and let $\mathcal C$ be a completely positive trace-preserving map on operators on $\mathcal H$. Let $0\le\varepsilon\le1$. Suppose every unit vector $\phi\in\mathcal H$ satisfies $\langle\phi|\mathcal C(|\phi\rangle\langle\phi|)|\phi\rangle\ge1-\varepsilon$. Then every unit vector $\psi\in\mathcal H_0\otimes\mathcal H$ satisfies
--
--   $$\langle\psi|(\mathrm{id}_{\mathcal H_0}\otimes\mathcal C)(|\psi\rangle\langle\psi|)|\psi\rangle\ge1-2\sqrt\varepsilon.$$
--
--   The overlap is squared fidelity with the pure input. This transfers a uniform pure-input fidelity guarantee to arbitrary entangled inputs. The source attributes the result to [66], reviewed in [67], and adapts the proof from [69].
--
--   **Formalization Note** Finite-dimensional spaces are represented in orthonormal coordinates with arbitrary nonempty finite index type. The reference is a second copy of that space. Universal inequalities over unit vectors express the displayed minimum inequalities without adding minimizer hypotheses.
-- source:
--   Energy-constrained private and quantum capacities of quantum channels, arXiv:1609.01997v2, PDF p. 26, Appendix A, Proposition 5 (A1–A2): minimum fidelity implies minimum entanglement fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P29

open Filter

-- PDF p.2, Eq.(2): reuse the accepted entropy in bits; its complete body
-- implements the same zero-occupation convention as this paper.

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF pp.26--27, Appendix A, Proposition 5, Eqs.(A1)--(A2).
In arbitrary positive finite dimension, a lower bound on every normalized pure-state
survival probability implies the stated bound on every normalized reference/input state.
The reference uses a second copy of the same coordinate space, identifying the source's
isomorphic `H0` with `H`. `effectProb (pureDensity psi)` is exactly the squared pure-state
fidelity, not its square root. Universal inequalities on the nonempty compact unit spheres
are equivalent to the source's minimum inequalities. Provenance: [66], reviewed in [67],
with the source's proof adapted from [69]. -/
theorem minimumFidelity_implies_minimumEntanglementFidelity
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (C : Superop I I) (hC : IsChannel C)
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hminimum : ∀ phi : EuclideanSpace ℂ I, IsState phi →
      1 - epsilon ≤ effectProb (pureDensity phi) (C (pureDensity phi))) :
    ∀ psi : EuclideanSpace ℂ (I × I), IsState psi →
      1 - 2 * Real.sqrt epsilon ≤
        effectProb (pureDensity psi)
          (idTensorSuperop (R := I) C (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P29

end
