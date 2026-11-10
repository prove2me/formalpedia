-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_profile_defect_distinct
-- name    : SmallClassesNeighbourhood.Linear.profile_defect_distinct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:36.361891+00:00
-- url     : https://prove2.me/theorems/3b0da2fc-1bfc-46f8-a6b5-ea745ff76537
-- title:
--   Observation 18 — profile–defect pairs distinguish good vertices
-- statement:
--   Fix the canonical selections of Section 3.2.1, with C_0 sufficiently large. For distinct good vertices u and v, their profiles P_u=N_Q(u), P_v=N_Q(v) and defects D_u=N_A(u)△Σ(u), D_v=N_A(v)△Σ(v) satisfy
--
--   $$(P_u,D_u)\ne(P_v,D_v).$$
--
--   Thus the tagged profile–defect graph records good vertices without merging edges. The profiles and defects are computed from the same representatives.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
--   - encoding: the fixed choices in Section 3.2.1 → CanonicalData with the minimal pair, maximal separated R, representatives and good vertices; reason: these are precisely the preceding source selections; profiles, defects and representative images are computed from them
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Observation 18, printed p. 15 (PDF p. 16)

import Definitions.Def_SmallClassesNeighbourhood_Linear_canonical

namespace SmallClassesNeighbourhood.Linear

theorem profile_defect_distinct :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C0 : ℕ, L ≤ C0 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (s : CanonicalData C0 F)
    (u v : V) (hu : u ∈ s.Bgood) (hv : v ∈ s.Bgood) (hne : u ≠ v),
    (s.P u, s.D u) ≠ (s.P v, s.D v) := by sorry

end SmallClassesNeighbourhood.Linear
