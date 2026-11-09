-- Prove2me | Theorems.Thm_PolyContract_fullPlane_existsUnique
-- name    : PolyContract.fullPlane_existsUnique
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:51:13.122011+00:00
-- url     : https://prove2.me/theorems/50cd7245-d25d-4e9c-9049-7f3b07c20dcf
-- title:
--   §B.6.1, p.28 — the full-plane best response $\xi^g(\alpha)$ exists and is unique
-- statement:
--   Let $g:2^E\to\mathbb R$ be submodular with $g(\emptyset)=0$, not necessarily monotone, on a finite nonempty $E$, and let $m,\beta\in\mathbb R^E_{>0}$. For every $\alpha\in\mathbb R$, the strictly concave function
--   $$y\mapsto\alpha\,m^\top y-\sum_e\beta_ey_e^2/2$$
--   has a unique maximizer $\xi^g(\alpha)$ on the full plane $B^{(\pm)}(g)=\{y: y(S)\le g(S)\ \forall S,\ y(E)=g(E)\}$.
--
--   This extends the best response to non-monotone submodular functions and to all shares, the setting of the translation tools used to build combs.
--
--   Differences from the source: none.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), App. B.6.1, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_PolyContract_FullPlane

set_option autoImplicit false

namespace PolyContract

/-- **§B.6.1, p.28: the full-plane best response exists and is unique** (Klimm, Lippke, Warode,
arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, App. B.6.1, p.28). Let
`g : 2^E → ℝ` be submodular with `g(∅) = 0`, not necessarily monotone, and `m, β ∈ ℝ^E_{>0}`.
"So for every `α ∈ ℝ` the strictly concave function `U_A(· | α)`, given on all of `ℝ^E` by the
same formula as on `P(+)(f)`, has a unique maximizer `ξ^g(α)` on `B(±)(g)`, the full-plane best
response of `g` (for `m` and `β`)."

**Formalization Note** The data `(g, m, β)` is the `QuadInstance` `⟨g, m, β⟩`. -/
theorem fullPlane_existsUnique {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (g : Finset ι → ℝ) (m β : ι → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g)
    (hg0 : g ∅ = 0) (hm : ∀ e, 0 < m e) (hβ : ∀ e, 0 < β e) (α : ℝ) :
    ∃! y : ι → ℝ, (⟨g, m, β⟩ : QuadInstance ι).IsFullPlaneBR α y := by sorry

end PolyContract
