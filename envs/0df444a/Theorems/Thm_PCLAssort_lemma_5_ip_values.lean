-- Prove2me | Theorems.Thm_PCLAssort_lemma_5_ip_values
-- name    : PCLAssort.lemma_5_ip_values
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:10.517687+00:00
-- url     : https://prove2.me/theorems/2d86b1de-049d-42fb-b6fa-4a4197327338
-- title:
--   Lemma 5 — optimal values of IP$_1(z)$ and IP$_2(z)$
-- statement:
--   Let $\mathcal F$ be a downward-closed family of assortments containing $\emptyset$, and $z\in\mathbb R$. Then
--
--   1. the optimal value of IP$_1(z)$ equals $f(z)=\max_{x\in\mathcal F}h_z(x)$;
--   2. the optimal value of IP$_2(z)$ equals the optimal max-dicut value on $G_z$ subject to the constraints that the dummy vertex is not selected and that the set of chosen vertices lies in $\mathcal F$:
--
--   $$
--   \mathrm{opt}\,\mathrm{IP}_2(z)=\max_{S\in\mathcal F}\sum_{(i,j)\in E:\ i\in S,\ j\notin S}w_{ij}(z).
--   $$
--
--   Differences from the source:
--   - reading: 𝓕 downward closed (p.790) → 𝓕 downward closed and ∅ ∈ 𝓕; reason: every constraint family of the paper contains ∅; with 𝓕 = ∅ the optimal values are undefined
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: R_ij(x) = 0/0 for an empty nest → Lean's 0/0 = 0; reason: the nest then has weight V_ij(x)^{γ_ij} = 0 (γ_ij > 0), so it contributes nothing either way
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 5, p.792 (PDF p.8)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_DownwardClosed
import Definitions.Def_PCLAssort_fValue
import Definitions.Def_PCLAssort_ip1Value
import Definitions.Def_PCLAssort_ip2Value
import Definitions.Def_PCLAssort_constrDicutValue
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight

namespace PCLAssort

/-- Lemma 5 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.792): the optimal value of IP₁(z) is exactly `f(z)`. The optimal value of
IP₂(z) is the optimal max-dicut value on `G_z` subject to the constraints that the dummy vertex is not
selected and that the set of chosen vertices lies in `𝓕`.

**Formalization Note.** `𝓕` is any downward-closed family containing `∅`, the paper's standing
assumption (p.790). -/
theorem lemma_5_ip_values {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n)))
    (hF : DownwardClosed F) (z : ℝ) :
    ip1Value I F z = fValue I F z ∧
      ip2Value I F z = constrDicutValue (pclEdges n) (pclWeight I z) F := by sorry

end PCLAssort
