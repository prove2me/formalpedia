-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_4_5
-- name    : RandProdExp.TwoSided.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:19:30.706731+00:00
-- url     : https://prove2.me/theorems/e5135cbd-f01e-4c0b-ae54-cc944e86011b
-- title:
--   Lemma 4.5 — extendable ⇔ inner-generated in the dual ⇔ $\pi_M$ onto ⇔ $\tau_M$ injective
-- statement:
--   Let $K$ be a field, $C_1,\dots,C_D\subseteq K^n$ codes, $B_i=C_i^\perp$, $C=C_1\otimes\cdots\otimes C_D$ and $B=B_1\boxplus\cdots\boxplus B_D$. For every set $M\subseteq[n]^D$ the following are equivalent:
--   1. $M$ is extendable in $C$;
--   2. $M$ is inner-generated in $B$;
--   3. the restriction map $\pi_M:C\to F(M)$ is surjective;
--   4. the corestriction map $\tau_M:K^M/\sum_{\ell\in L(M)}B_\ell\to K^{[n]^D}/B$ is injective.
--
--   $$\text{(1)}\iff\text{(2)}\iff\text{(3)}\iff\text{(4)}.$$
--   This is the duality that turns inner-generatedness of the check-product code into a statement about one linear map.
--
--   Differences from the source:
--   - encoding: standing assumption of §3.1 (p. 19): integers D ≥ 1 and n ≥ 2 → explicit hypotheses 1 ≤ D and 2 ≤ n; reason: stated once at the top of §3.1 for the whole paper; makes the anchor of a plane unique
--   - encoding: codes C_i = Im(G_i^⊤) with dim C_i = k_i, generator matrices G_i chosen first (§4.1) → arbitrary subspaces C_i ⊆ K^n; reason: every subspace has a full-rank generator matrix with k_i = dim C_i; the statement does not involve G_i
--   - encoding: K^M, F(M) ⊆ K^M and π_M : C → F(M), c ↦ c|_M → words vanishing outside M; π_M(c) = the word equal to c on M and 0 outside; reason: extension by zero is a linear isomorphism from K^M onto these words
--   - encoding: τ_M as a colimit map (Eq. (11)), equivalently induced by extension by zero ι_M (Fact 4.4) → Submodule.mapQ of the inclusion of the supported words, from (supported M)/Σ_{ℓ∈L(M)} B_ℓ to K^{[n]^D}/B; reason: the concrete quotient form the paper itself uses in Fact 4.4
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 30, Lemma 4.5

import Mathlib
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Codes

namespace RandProdExp.TwoSided

/-- **Lemma 4.5** (p. 30). For codes `C_1, …, C_D ⊆ K^n` over a field `K`, `B_i = C_i^⊥`, and any set
`M ⊆ [n]^D`, the following are equivalent:
1. `M` is extendable in `C = C_1 ⊗ ⋯ ⊗ C_D`;
2. `M` is inner-generated in `B = B_1 ⊞ ⋯ ⊞ B_D`;
3. the restriction map `π_M : C → F(M)` is surjective;
4. the corestriction map `τ_M : K^M / Σ_{ℓ ∈ L(M)} B_ℓ → K^{[n]^D} / B` is injective.
(Standing assumptions of §3.1: `D ≥ 1`, `n ≥ 2`.) -/
theorem lemma_4_5 {K : Type} [Field K] (D n : ℕ) (hD : 1 ≤ D) (hn : 2 ≤ n)
    (C : Fin D → Submodule K (Fin n → K)) (M : Set (Fin D → Fin n)) :
    List.TFAE [Extendable M C, InnerGenerated M (fun i => GoodQLTC.dualCode (C i)),
      Function.Surjective (restrictionMap M C), Function.Injective (tauMap M C)] := by sorry

end RandProdExp.TwoSided
