-- Prove2me | Theorems.Thm_StrongCosmicCensorship_timelike_complete_globally_hyperbolic_c0_inextendible
-- name    : StrongCosmicCensorship.timelike_complete_globally_hyperbolic_c0_inextendible
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T02:01:01.428794+00:00
-- url     : https://prove2.me/theorems/65845fdf-356a-40d2-ba65-5ecf4393714c
-- title:
--   Theorem 3.1 — timelike geodesically complete and globally hyperbolic implies $C^0$-inextendible
-- statement:
--   Theorem 3.1 of the source states, verbatim:
--
--   > A smooth (at least $C^2$) time-oriented Lorentzian manifold that is time-like geodesically complete and globally hyperbolic is $C^0$-inextendible.
--
--   Formally: let $U\subseteq\mathbb{R}^4$ be open and let $g$ be a metric field on it. Suppose
--
--   1. $(U,g)$ is a smooth Lorentzian spacetime;
--   2. $(U,g)$ is time-oriented, i.e. carries a continuous timelike vector field;
--   3. $(U,g)$ is timelike geodesically complete;
--   4. $(U,g)$ is globally hyperbolic, i.e. admits a Cauchy hypersurface.
--
--   Then $(U,g)$ admits no $C^0$ extension: there is no open $V$, continuous Lorentzian metric $h$ on $V$ and injective $C^1$ immersion $J:U\to V$ with
--   $$g = (DJ)^{\mathsf T}\,(h\circ J)\,DJ$$
--   whose image has nonempty boundary inside $V$.
--
--   **Why this is the mission's goal.** The subject of the source is Conjecture 1.1, Strong Cosmic Censorship: *for generic, asymptotically flat, complete and regular initial data, the maximal globally hyperbolic development is inextendible as a solution to the Einstein equations.* That conjecture is deliberately **not** stated in this proposal. It quantifies over the maximal globally hyperbolic development of *generic* data, and the source is explicit that “the precise definitions of ‘generic,’ ‘regular,’ and ‘solutions’ are left intentionally vague to allow flexibility in solving the conjecture.” Any Lean rendering would have to supply a definition of genericity the source does not give, and a formal statement resting on an invented or opaque genericity predicate asserts nothing. Conjecture 1.1 is therefore carried in the mission description in prose.
--
--   Theorem 3.1 is the strongest statement in the source that *can* be rendered faithfully here: it is precisely stated, involves no genericity and no maximal development, and the source identifies its role in the programme directly — it “shows that in proving Conjecture 1.1, one can now restrict our attention to timelike geodesically incomplete spacetimes.”
--
--   **Framework scope.** Every statement in this proposal is set in a purpose-built *single-chart coordinate framework*, not in abstract Lorentzian geometry. Mathlib contains no Lorentzian geometry whatsoever — no Lorentzian metrics, no affine connection, no Riemann or Ricci curvature, no causal structure, no global hyperbolicity, no maximal globally hyperbolic development — so all of it is defined from scratch in the accompanying definition item. A *spacetime* here is an open subset $U \subseteq \mathbb{R}^4$ together with a field of $4 \times 4$ real matrices $g_{ab}(x)$ of signature $(-,+,+,+)$. This is fully precise and auditable, but it is **strictly less general than the abstract Lorentzian manifolds of the source**: only chart-representable spacetimes, and only chart-representable extensions, are quantified over.
-- source:
--   Maxime Van de Moortel, "The Strong Cosmic Censorship Conjecture", arXiv:2501.13180v2 [gr-qc], 10 Oct 2025, https://arxiv.org/abs/2501.13180, Section 3.1, Theorem 3.1 (attributed there to reference [40]); inextendibility notion from Statement I of Section 2.3

import Definitions.Def_scc_coordinate_framework
open Set Filter
open scoped Matrix Topology

namespace StrongCosmicCensorship

/-- **Goal.** A smooth, time-oriented, timelike geodesically complete, globally
hyperbolic Lorentzian spacetime admits no `C⁰` extension. -/
theorem timelike_complete_globally_hyperbolic_c0_inextendible
    (U : Set Coords) (g : MetricField)
    (hst : IsSpacetime U g) (hto : IsTimeOriented U g)
    (hgc : TimelikeGeodesicallyComplete U g) (hgh : IsGloballyHyperbolic U g) :
    IsC0Inextendible U g := by sorry

end StrongCosmicCensorship
