-- Prove2me | Theorems.Thm_VAS5Reach_Supplement_theorem_B_1
-- name    : VAS5Reach.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:51:13.457435+00:00
-- url     : https://prove2.me/theorems/ed1922ff-4f8f-4cdf-a001-818a6f9cf747
-- title:
--   Theorem B.1 — $\mathcal T_C$ with $C=2d\|T\|(\|T\|+1)$ is a transformation area
-- statement:
--   Let $V$ be a $d$-VAS with transition set $T$, let $\|T\|=\max_{a\in T}\|a\|$ ($0$ if $T=\emptyset$) and
--   $$C=2d\,\|T\|\,(\|T\|+1).$$
--   Then $\mathcal T_C=\bigcup_{i\in[d]}\{x\in\mathbb N^d:x(j)\ge C\text{ for all }j\ne i\}$ is a transformation area of $V$: for all $s,t\in\mathcal T_C$ (possibly in different sets $\mathcal T^i_C$, $\mathcal T^j_C$) and every word $\pi\in T^*$ with $s+\mathrm{EFF}(\pi)=t$, there is a run $s\xrightarrow{\rho}t$ in $V$ with $\psi_\rho=\psi_\pi$.
--
--   This makes van Leeuwen's transformation area quantitative: van Leeuwen gave, for each $i$, a computable threshold for $\mathcal T^i_C$; here the threshold is explicit, polynomial in $d$ and $\|T\|$, and the union over $i$ is a transformation area.
--
--   Differences from the source:
--   - encoding: coordinates [d] of a d-VAS → an arbitrary finite type ι with d = Fintype.card ι; reason: convention of the published base definitions; ι = Fin d is the paper's case and every finite type is equivalent to one
--   - encoding: ψ_ρ = ψ_π (same Parikh image) → parikh ρ = parikh π with the published VAS5Reach.parikh (occurrence counts of every vector); reason: the Parikh image counts occurrences of each transition; equal counts is the same condition
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), App. B, Theorem B.1, p.46 (PDF p.48); proof p.47 (PDF p.49)

import Mathlib
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_Supplement_IsTransArea

namespace VAS5Reach.Supplement

open VAS5Reach

/-- **Theorem B.1.** Let `C := 2d∥T∥(∥T∥ + 1)`. Then `T_C` is a transformation area of `V`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), App. B "Quantifying van
Leeuwen's Transformation Area", Theorem B.1, printed p. 46 (PDF p. 48); proof printed p. 47
(PDF p. 49).

For every `d`-VAS `V` with transition set `T` (`d = Fintype.card ι`), the set
`T_C = ⋃_i {x ∈ ℕ^d : x(j) ≥ C for all j ≠ i}` with `C = 2d∥T∥(∥T∥ + 1)` is a transformation area:
every `ℤ`-run between two of its points (possibly in different `T^i_C`, `T^j_C`) can be reordered
into a run of `V` with the same Parikh image.

**Formalization Note** `∥T∥` is the published `normT` (max norm, `0` for `T = ∅`); coordinates
form an arbitrary finite type `ι`. -/
theorem theorem_B_1 {ι : Type} [Fintype ι] (T : Finset (ι → ℤ)) :
    IsTransArea T (TC (2 * Fintype.card ι * normT T * (normT T + 1))) := by sorry

end VAS5Reach.Supplement
