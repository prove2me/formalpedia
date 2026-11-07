-- Prove2me | Theorems.Thm_SteinerAPX_theorem_7
-- name    : SteinerAPX.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:51.413604+00:00
-- url     : https://prove2.me/theorems/34032809-8665-4594-8029-bab312285d60
-- title:
--   Theorem 7 (cable reduction) — $L+\frac43|U|-\Delta\nu(H)-C_2\rho L\le\mathrm{OPT}(P_\rho)\le L+\frac43|U|-\Delta\nu(H)$
-- statement:
--   There is an absolute constant $C_2$ such that, for every well-formed, separated cable layout of a 3DM-3 instance $H=(U,E)$ in some $\mathbb R^D$ with total cable length $L$, and every $0<\rho\le1/100$,
--   $$
--   L+\tfrac43|U|-\Delta\,\nu(H)-C_2\rho L\ \le\ \mathrm{OPT}(P_\rho)\ \le\ L+\tfrac43|U|-\Delta\,\nu(H),
--   $$
--   where $\Delta=4-\sqrt2-\sqrt6$ and $|U|=3r$.
--
--   Up to an error $O(\rho L)$, the Steiner optimum on the sampled terminals is the cable length plus the cost of connecting the cables, which encodes the maximum matching size; any separated routing of small total length therefore yields a gap reduction.
--
--   Differences from the source:
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Theorem 7, eq. (1), §4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_samples

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Theorem 7 (cable reduction), eq. (1).** S. Bartlmae, *Inapproximability of Euclidean
Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Theorem 7, p.14 (PDF p.16):
"There is an absolute constant C2 such that, for separated cables and every 0 < ρ ≤ 1/100,
L + (4/3)|U| − ∆ν(H) − C2ρL ≤ OPT(Pρ) ≤ L + (4/3)|U| − ∆ν(H). (1)"

There is a constant `C₂` such that for every well-formed, separated layout of a 3DM-3 instance `H`
in any `ℝᴰ`, with total cable length `L`, and every `0 < ρ ≤ 1/100`,
`L + (4/3)|U| − ∆ν(H) − C₂ρL ≤ OPT(Pρ) ≤ L + (4/3)|U| − ∆ν(H)`, where `|U| = 3r` and
`∆ = 4 − √2 − √6`.

**Formalization Note** `C₂` is chosen before the dimension, the instance, the layout and `ρ`.
`OPT` is `opt`, the infimum over networks spanning `Pρ`. -/
theorem theorem_7 :
    ∃ C₂ : ℝ, ∀ {ι : Type} [Fintype ι] (H : Inst3DM) (L : CableLayout H (EuclideanSpace ℝ ι)),
      H.IsThreeDM3 → L.WellFormed → Separated L →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 100 →
      L.totalLen + 4 / 3 * (3 * (H.r : ℝ)) - Delta * (H.nu : ℝ) - C₂ * ρ * L.totalLen ≤
          opt (samples L ρ) ∧
        opt (samples L ρ) ≤ L.totalLen + 4 / 3 * (3 * (H.r : ℝ)) - Delta * (H.nu : ℝ) := by sorry

end SteinerAPX
