-- Prove2me | Theorems.Thm_RandGraphStates_proposition_4_11
-- name    : RandGraphStates.proposition_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:14.933865+00:00
-- url     : https://prove2.me/theorems/b8672176-f16e-45c3-9c1a-954c1f730aac
-- title:
--   Proposition 4.11: sparse pivot deletion
-- statement:
--   For $1\le j_0,L_0,t\le m$, let $\Delta$ be either diagonal or symmetric with zero diagonal, and $M=A_m(p)+\Delta$. Then
--   $$
--   \sup_\Delta\Pr\bigl(\mathrm{Nullity}(M)\ge t,\ \mathcal E^{\mathrm{sp}}_{j_0,L_0}(M)\bigr)\le m\sum_{\ell=1}^{L_0}\binom m\ell\,p_+^{\,j_0-1}\,\pi^p_{m-1}(t-1)
--   $$
--   when $\Delta$ is diagonal, and the same bound with $\Pi^p_{m-1}(t-1)$ in place of $\pi^p_{m-1}(t-1)$ when $\Delta$ is symmetric with zero diagonal.
--
--   The bound retains a nullity tail of order $m-1$ at threshold $t-1$, which allows a recursive application.
--
--   Differences from the source:
--   - encoding: sup_Δ Pr(…) ≤ B → ∀ Δ in the family: Pr(…) ≤ B; reason: a supremum is at most B exactly when every term is
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Proposition 4.11, p.26

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Proposition 4.11** (sparse pivot deletion). For `1 ≤ j₀, L₀, t ≤ m` and `M = A_m(p) + Δ`,
`sup_Δ Pr(Nullity(M) ≥ t, E^sp_{j₀,L₀}(M)) ≤ m Σ_{ℓ=1}^{L₀} C(m,ℓ) p₊^{j₀-1} π^p_{m-1}(t-1)` for `Δ` diagonal,
and the same with `Π^p_{m-1}(t-1)` for `Δ` symmetric with zero diagonal.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Proposition 4.11, p.26.

**Formalization Note.** A supremum at most `B` is written as a bound for every `Δ`. The natural-number
subtractions `m - 1`, `t - 1`, `j₀ - 1` are exact under `1 ≤ j₀, t ≤ m`. `0 < p < 1` is the standing
assumption of §4, p.17. -/
theorem proposition_4_11 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m j0 L0 t : ℕ)
    (hj0 : 1 ≤ j0) (hL0 : 1 ≤ L0) (ht : 1 ≤ t) (hj0m : j0 ≤ m) (hL0m : L0 ≤ m) (htm : t ≤ m) :
    (∀ d : Fin m → ZMod 2,
      gnpProb m p (fun G => t ≤ nullity (adjF2 G + Matrix.diagonal d) ∧
          Esp j0 L0 (adjF2 G + Matrix.diagonal d)) ≤
        (m : ℝ) * (∑ l ∈ Finset.Icc 1 L0, (m.choose l : ℝ)) * pPlus p ^ (j0 - 1) *
          piTail p (m - 1) (t - 1)) ∧
    (∀ Γ : ZeroDiagSymm m,
      gnpProb m p (fun G => t ≤ nullity (adjF2 G + Γ.1) ∧ Esp j0 L0 (adjF2 G + Γ.1)) ≤
        (m : ℝ) * (∑ l ∈ Finset.Icc 1 L0, (m.choose l : ℝ)) * pPlus p ^ (j0 - 1) *
          bigPiTail p (m - 1) (t - 1)) := by sorry

end RandGraphStates
