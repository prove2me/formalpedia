-- Prove2me | Theorems.Thm_SSNonExt_lemma_3_3_error_identity
-- name    : SSNonExt.lemma_3_3_error_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:01:37.558198+00:00
-- url     : https://prove2.me/theorems/8a6f96ba-780a-4a8c-9644-b43d35f30bb8
-- title:
--   Proof of Lemma 3.3 — the error of a one-bit $\mathrm{Ext}$ on $P_T$ is $|H_T|/(2Z_T)$
-- statement:
--   Let $b\ge2$ and let $\mathrm{Ext}:\mathcal K\to\{0,1\}$ be any function on the key set of $\Pi_b$. Put $h(k)=(-1)^{\mathrm{Ext}(k)}$ and, for $T\subseteq V$,
--
--   $$H_T=\sum_{k\in\Omega_T}h(k)=\sum_{i\in T}h(C_i)+\sum_{i\in T^c}\big(h(L_i)+h(R_i)\big).$$
--
--   Then for $K\sim P_T$,
--
--   $$\mathrm{TV}\big(\mathrm{Ext}(K),U_1\big)=\frac{|H_T|}{2Z_T},\qquad Z_T=|\Omega_T|.$$
--
--   The statement has two parts: the second equality in the definition of $H_T$, and the distance identity.
--
--   Differences from the source:
--   - encoding: Ext : 𝒦 → {0,1} and U₁ the uniform law on {0,1}^1 → Ext : Key b → Bool and the uniform law on Bool; reason: {0,1}^1 and Bool are the same two-point set
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), proof of Lemma 3.3, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_Hsum

namespace SSNonExt

/-- **Proof of Lemma 3.3, the error identity.** "Let h(k) = (−1)^{Ext(k)} and, for T ⊆ V, let
H_T := ∑_{k∈Ω_T} h(k) = ∑_{i∈T} h(C_i) + ∑_{i∈T^c} (h(L_i) + h(R_i)). For K ∼ P_T the distance of
Ext(K) from U₁ equals |H_T|/(2Z_T)."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), proof of Lemma 3.3, p.7 (PDF p.7).

Standing hypothesis of §3: `b ≥ 2`. `Z_T = |Ω_T|`.

**Formalization Note.** A one-bit extractor is `Ext : 𝒦 → Bool` and `U₁` is the uniform law on
`Bool` (`{0,1}¹ ≅ {0,1}`). The two conclusions are the second equality of the `H_T` display and the
distance identity. -/
theorem lemma_3_3_error_identity (b : ℕ) (hb : 2 ≤ b) (Ext : Key b → Bool) (T : Finset (V b)) :
    Hsum Ext T = ∑ i ∈ T, hSign Ext (Branch.C, i) +
        ∑ i ∈ Tᶜ, (hSign Ext (Branch.L, i) + hSign Ext (Branch.R, i)) ∧
      TV ((srcP T).map Ext) (PMF.uniformOfFintype Bool) =
        |(Hsum Ext T : ℝ)| / (2 * ((Omega T).card : ℝ)) := by sorry

end SSNonExt
