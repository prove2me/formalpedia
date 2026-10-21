-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_constructed_semi_admissible
-- name    : QAlgorithms.Papers.Independent.Support21.P12.constructed_semi_admissible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:15:43.505354+00:00
-- url     : https://prove2.me/theorems/8de481ed-0c25-4030-80dc-d8a2f6460c35
-- title:
--   Construction of semi-admissible degenerate parameters
-- statement:
--   Let $S$ be an integral domain in which two is invertible, let $0<d<r$, and choose $u_1,\ldots,u_r\in S$. Require $u_i\ne u_j$ for distinct indices, $u_i\ne-u_j$ for all indices, and $u_i\ne\pm\tfrac12$ for every i. Define the sequence using the integral eta polynomials on the first d roots:
--
--   $$\omega_a=\eta_a^+(u_1,\ldots,u_d)\qquad(a\ge0).$$
--
--   Assume the whole left ideal $N_{2,S,r}e_1$ is torsion free. Then these degree-r parameters are d-semi-admissible: $(y_1^je_1)_{0\le j<d}$ is S-linearly independent, whereas the family through degree d is dependent.
--
--   **Source correction** The printed plus-separation condition includes equal indices and would be impossible. It is restricted to distinct indices; minus separation still includes equal indices and excludes zero roots. Independent moderation of this correction remains pending.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 22, Unnumbered construction in Section 8

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

universe u

/-- Section 8 construction, PDF p.22. Printed 'u_i≠±u_j for any i,j' is
corrected to distinct-index plus separation and all-index minus separation:
the former is otherwise impossible at i=j, while the latter excludes zero.
Assumption 5.1 from 'From here on' on p.10 is retained. This correction needs
independent moderation; no such moderation is claimed by this drafting stage. -/
theorem constructed_semi_admissible (S : Type*) [CommRing S] [IsDomain S]
    (r d : ℕ) (hd : 0 < d) (hdr : d < r) (u : Fin r → S)
    (two : Sˣ) (htwo : (↑two : S) = 2)
    (hplus : Function.Injective u) (hminus : ∀ i j : Fin r, u i ≠ -u j)
    (hhalf : ∀ i : Fin r, u i ≠ (↑(two⁻¹) : S) ∧ u i ≠ -(↑(two⁻¹) : S))
    (htor : IdealTorsionFree S
      (fun a => evalIntegral (firstRoots u (Nat.le_of_lt hdr)) (universalOmega d a))
      .degenerate r u) :
    SemiAdmissible S
      (fun a => evalIntegral (firstRoots u (Nat.le_of_lt hdr)) (universalOmega d a))
      .degenerate r u d := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
