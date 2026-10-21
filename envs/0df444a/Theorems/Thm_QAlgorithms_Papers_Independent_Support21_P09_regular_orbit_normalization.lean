-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_regular_orbit_normalization
-- name    : QAlgorithms.Papers.Independent.Support21.P09.regular_orbit_normalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:44:22.421115+00:00
-- url     : https://prove2.me/theorems/2ed59dd3-09c4-4a87-8255-99245d498536
-- title:
--   Regular orbit symmetry and irreducible normalization
-- statement:
--   Let $G$ be finite, $d>0$, $\phi:G\to U(d)$ ordinary, and $v\in\mathbb C^d$. Define the full group-indexed matrix $M_v$ by $(M_v)_{i,g}=(\phi(g)v)_i$ and let $L(h)e_g=e_{hg}$ be the left regular action. Then
--
--   $$
--   \phi(h)M_v=M_vL(h)\qquad(h\in G).
--   $$
--
--   If $\phi$ is irreducible and $\|v\|_2^2=d/|G|$, its nonzero orbit columns define a POVM, equivalently
--
--   $$
--   \sum_{g\in G}\phi(g)vv^\dagger\phi(g)^\dagger=I_d.
--   $$
--
--   The orbit symmetry therefore has no additional column phases. Full group indexing is essential to this regular action and to the stated normalization; repeated effects are retained.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 9, §3: regular orbit symmetry and irreducible orbit normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF p.9: full-group orbit columns have left regular symmetry with no phases.
The irreducible orbit normalization is squared norm d/|G|, rather than unit norm. -/
theorem regular_orbit_normalization
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (hphi : UnitaryRep phi) (v : Fin d → ℂ) :
    MatrixIntertwines phi groupLeftRegular (orbitMatrix phi v) ∧
    (Irreducible phi → (∑ i, ‖v i‖ ^ 2) = (d : ℝ) / Fintype.card G →
      RankOnePOVM (orbitMatrix phi v)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
