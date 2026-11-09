-- Prove2me | Theorems.Thm_SSNonExt_lemma_3_3
-- name    : SSNonExt.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:01:29.16423+00:00
-- url     : https://prove2.me/theorems/941fabcd-9337-4d0f-8329-1ce46cbf3ce6
-- title:
--   Lemma 3.3 — no bit can be extracted: error $\ge1/6$ on $P_T$ or $P_{T^c}$
-- statement:
--   Let $b\ge2$. For every function $\mathrm{Ext}:\mathcal K\to\{0,1\}$ on the key set $\mathcal K=\{L,R,C\}\times\mathbb F_{2^b}$ there is $T\subseteq V$ such that
--
--   $$\mathrm{TV}\big(\mathrm{Ext}(K),U_1\big)\ge\frac16\ \text{ for }K\sim P_T\qquad\text{or}\qquad\mathrm{TV}\big(\mathrm{Ext}(K),U_1\big)\ge\frac16\ \text{ for }K\sim P_{T^c},$$
--
--   where $T^c=V\setminus T$. The extractor is arbitrary (no computational restriction).
--
--   Differences from the source:
--   - encoding: Ext : 𝒦 → {0,1} and U₁ the uniform law on {0,1}^1 → Ext : Key b → Bool and the uniform law on Bool; reason: {0,1}^1 and Bool are the same two-point set
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Lemma 3.3, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_sourceClass

namespace SSNonExt

/-- **Lemma 3.3 (No bit can be extracted).** "For every Ext : 𝒦 → {0, 1} there is T ⊆ V such that Ext
has statistical error at least 1/6 on P_T or on P_{T^c}, where T^c = V \ T."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Lemma 3.3, p.7 (PDF p.7).

Standing hypothesis of §3: `b ≥ 2` (the lemma does not involve `α`).

**Formalization Note.** The statistical error of `Ext` on `P` is `TV(Ext(K), U₁)`, `K ∼ P`, with
`U₁` the uniform law on `Bool`. The extractor is an arbitrary function. -/
theorem lemma_3_3 (b : ℕ) (hb : 2 ≤ b) (Ext : Key b → Bool) :
    ∃ T : Finset (V b),
      (1 / 6 : ℝ) ≤ TV ((srcP T).map Ext) (PMF.uniformOfFintype Bool) ∨
        (1 / 6 : ℝ) ≤ TV ((srcP Tᶜ).map Ext) (PMF.uniformOfFintype Bool) := by sorry

end SSNonExt
