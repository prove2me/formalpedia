-- Prove2me | Theorems.Thm_PhilipponMultiplicity_connected_pointed_stabilizer_bound
-- name    : PhilipponMultiplicity.connected_pointed_stabilizer_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-10T14:47:27.747608+00:00
-- url     : https://prove2.me/theorems/90796df0-821b-4182-a53d-dce577a84278
-- title:
--   Connected pointed stabilizer: sampled contact and a binomial degree bound
-- statement:
--   Let $G$ be a connected product of embedded commutative algebraic groups over a Philippon base field, and let $A$ be an analytic subgroup. Write $n=\dim G$. Suppose $C$ is the actual Section 5 input: it includes a finite sample $\Sigma$ containing zero, contact parameter $T$, a multihomogeneous polynomial $P$ of multidegree $D$ with order at least $nT+1$ on $\Sigma(n)$, and translation atlases bounded by the factor degrees $c_i$. Assume that $P$ is not identically zero on $G$.
--
--   There is a connected algebraic subgroup $H$ incompletely defined by equations of multidegrees at most $(c_iD_i)_i$, such that $P$ has order at least $T+1$ at every point of every sampled coset $g+H$, and
--   $$
--   \binom{T+s}{s}\,\mathcal H(H;D)\leq \mathcal H(G;(c_iD_i)_i),
--   \qquad s=\operatorname{codim}_A(A\cap H).
--   $$
--
--   This is an auxiliary result obtained while investigating the sampled-translates addendum. The bound does **not** include the number of sampled cosets. A separately checked connected additive-plane counterexample shows that this missing factor cannot be inserted under the proposed connected hypotheses. The original broad statement and its accepted disproof are preserved. Connectedness is an explicitly labelled hypothesis of this auxiliary theorem, not a claim that it is printed verbatim in the 1987 addendum.
-- source:
--   Auxiliary partial result derived for the connected correction. Philippon (1986), Section 5, pp. 380–382, https://numdam.org/articles/10.24033/bsmf.2060/; compare the origin-component observation in Philippon (1987), p. 398, https://numdam.org/articles/10.24033/bsmf.2084/. This is not the complete sampled-translates addendum and does not assert its coset-count factor.

import Definitions.Def_PhilipponMultiplicity_SectionFive

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem connected_pointed_stabilizer_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (C : SectionFiveInput G A)
    (hG : @_root_.IsConnected _ G.zariskiTopology Set.univ)
    (hP : ∃ x : G.Point, x ∉ zeroLocusOnGroup G C.polynomial) :
    ∃ H : AlgebraicSubgroup G,
      H.IsConnected ∧ HasIncompleteDefinition G H.carrier C.scaledDegrees ∧
      (∀ g ∈ C.samplingSet, ∀ h ∈ H.carrier,
        ((C.contactParameter+1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A C.polynomial (g+h)) ∧
      ((Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier) : ℝ) * hilbertDegreeForm G H.carrier C.degrees ≤
          hilbertDegreeForm G Set.univ C.scaledDegrees) := by sorry

end PhilipponMultiplicity
