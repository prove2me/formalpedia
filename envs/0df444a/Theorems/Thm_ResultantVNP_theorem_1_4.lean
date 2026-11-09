-- Prove2me | Theorems.Thm_ResultantVNP_theorem_1_4
-- name    : ResultantVNP.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:14.989366+00:00
-- url     : https://prove2.me/theorems/5c7c7594-6248-409b-a757-48e52a6a9fe7
-- title:
--   Theorem 1.4 — poly-size circuits for $\mathrm{Res}^{(2)}_n$ imply $\mathrm{VP}=\mathrm{VNP}$
-- statement:
--   **Algebraic hardness of resultants.** If the polynomial family $\{\mathrm{Res}^{(2)}_n\}_{n\ge1}$ of resultants of $n$ quadratic forms in $n$ variables has poly($n$)-size arithmetic circuits over $\mathbb C$, then
--
--   $$
--   \mathrm{VP}=\mathrm{VNP}.
--   $$
--
--   Only the circuit size is assumed polynomial: $\mathrm{Res}^{(2)}_n$ has degree $n2^{n-1}$, so it is not itself in VP or VNP. The theorem says that small circuits for the resultant would refute Valiant's hypothesis $\mathrm{VP}\ne\mathrm{VNP}$.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: poly(n)-size arithmetic circuits over ℂ → HasPolySizeCircuits: ∃ c, ∀ n ≥ 1, a fan-in-two circuit with complex constants and at most c·n^c + c gates computes Res^{(2)}_n mapped to ℂ[u]; reason: Section 3.1 conventions; c·n^c + c dominates every polynomial; size only, as printed
--   - encoding: VP and VNP → sets of PolyFamily (number of variables, p_n over Fin (nvars n)); VNP with g_n on exactly nvars n + q n variables; reason: Section 3.1 definitions
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.4, p.6 (proof p.17)

import Mathlib
import Definitions.Def_ResultantVNP_quadRes
import Definitions.Def_ResultantVNP_HasPolySizeCircuits
import Definitions.Def_ResultantVNP_VNP

namespace ResultantVNP

/-- **Theorem 1.4 (Algebraic hardness of resultants).** If the polynomial family `{Res^{(2)}_n}_{n≥1}`
has poly(n)-size arithmetic circuits over `ℂ`, then `VP = VNP`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.4, p.6 (proof p.17).

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `Res^{(2)}_n ∈ ℤ[u]` is mapped to `ℂ[u]`; "poly(n)-size" is `HasPolySizeCircuits` (size only, no
degree bound). `VP = VNP` is the equality of the two classes of polynomial families of Section 3.1. -/
theorem theorem_1_4 (𝓡 : ResultantSystem)
    (h : HasPolySizeCircuits (fun n => MvPolynomial.map (Int.castRingHom ℂ) (quadRes 𝓡 n))) :
    VP = VNP := by sorry

end ResultantVNP
