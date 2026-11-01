-- Prove2me | Theorems.Thm_ToricMemory_torus_sap_count
-- name    : ToricMemory.torus_sap_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:42.32099+00:00
-- url     : https://prove2.me/theorems/48bb40eb-26cc-4b53-917f-1751095828bb
-- title:
--   Eq. (58) on the torus — $n_{\rm SAP}(H,V)\le P_3(H+V)\,\mu_3^{H+V}$ uniformly in $L,T$
-- statement:
--   There are a constant $C$ and an integer $k\ge0$ such that for all $L,T\ge1$, every starting site $s$ of the $L\times L\times T$ torus and all $H,V\ge0$, the number of rooted self-avoiding polygons on the torus starting at $s$ with $H$ horizontal and $V$ vertical links satisfies
--   $$
--   n_{\rm SAP}(H,V)\;\le\;C(H+V+1)^k\,\mu_3^{H+V}.
--   $$
--   The constants do not depend on $L$ or $T$.
--
--   This is the bound with which the paper passes from (55), which counts polygons on the torus, to (59), using (58), which counts polygons in $\mathbb Z^3$: "an SAP with $H$ horizontal and $V$ vertical links has $\ell=H+V$ total links".
--
--   Differences from the source:
--   - reading: invoke eq. (58) (polygons in ℤ³) together with eq. (55) (polygons on the torus) → n_SAP(H, V) on the torus ≤ C(H + V + 1)^k μ₃^{H+V} with C, k independent of L and T; reason: (55) counts torus polygons, and (59) uses a bound P₃(H + V)μ₃^{H+V} for them uniform in L, T; this is the statement the step needs
--   - reading: μ₃ ≈ 4.684 (eq. (58)) → mu3 := inf_{n ≥ 1} c_n^{1/n}, the exact connective constant of ℤ³; reason: the decimal is the numerical value of the cubic lattice's connective constant, which is what the bound (58) is about
--   - encoding: P₃(H + V) a polynomial → C(H + V + 1)^k; reason: bounds every polynomial on ℕ
--   - encoding: a specified starting site → every site s; reason: the count does not depend on the site (vertex-transitivity)
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V C, p. 20 ("Since an SAP with H horizontal and V vertical links has ℓ = H + V total links, we may invoke eq. (58) together with eq. (55)")

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_CubicSAW
import Definitions.Def_ToricMemory_TorusSAP

namespace ToricMemory

/-- **Eq. (58) applied on the torus**, arXiv:quant-ph/0110143v1, Sec. V C, p. 20 (PDF p. 20):
"Since an SAP with `H` horizontal and `V` vertical links has `ℓ = H + V` total links, we may
invoke eq. (58) together with eq. (55)". There are `C` and `k`, independent of `L` and `T`, such
that for all `L, T ≥ 1`, every starting site `s` and all `H, V`, the number of rooted
self-avoiding polygons on the `L × L × T` torus with `H` horizontal and `V` vertical links is at
most `C (H + V + 1)^k μ₃^{H+V}`.

**Formalization Note** (55) counts polygons on the torus, (58) polygons in `ℤ³`; this item is
the bound with which the paper passes from one to the other. `C` and `k` are quantified before
`L` and `T`. -/
theorem torus_sap_count : ∃ C : ℝ, ∃ k : ℕ, ∀ (L T : ℕ) [NeZero L] [NeZero T]
    (s : Site L T) (H V : ℕ),
    (sapTorus L T s H V : ℝ) ≤ C * ((H + V : ℕ) + 1 : ℝ) ^ k * mu3 ^ (H + V) := by sorry

end ToricMemory
