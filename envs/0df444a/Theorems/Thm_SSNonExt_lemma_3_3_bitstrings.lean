-- Prove2me | Theorems.Thm_SSNonExt_lemma_3_3_bitstrings
-- name    : SSNonExt.lemma_3_3_bitstrings
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:03:39.211104+00:00
-- url     : https://prove2.me/theorems/5a439a29-2a8b-4638-beba-635385406ab9
-- title:
--   Proof of Theorem 1.1 — Lemma 3.3 for one-bit extractors on $\{0,1\}^{b+2}$
-- statement:
--   Let $b\ge2$ and fix the bit-string encoding of keys (two branch bits, then $\iota(i)$ for a bijection $\iota:\mathbb F_{2^b}\to\{0,1\}^b$), with $P_T$ the law of the encoded key under $U_{\Omega_T}$. For every function $\mathrm{Ext}:\{0,1\}^{b+2}\to\{0,1\}$ there is $T\subseteq V$ such that $\mathrm{Ext}$ has statistical error at least $1/6$ on $P_T$ or on $P_{T^c}$:
--
--   $$\max\Big\{\mathrm{TV}\big(\mathrm{Ext}(K),U_1\big)_{K\sim P_T},\ \mathrm{TV}\big(\mathrm{Ext}(K),U_1\big)_{K\sim P_{T^c}}\Big\}\ge\frac16.$$
--
--   The extractor may take any values on the fourth branch; the sources never charge it.
--
--   Differences from the source:
--   - reading: the lemma applies verbatim to functions on {0,1}^{b+2} → for every Ext : {0,1}^{b+2} → Bool there is T with error ≥ 1/6 on the bit-string P_T or P_{T^c}; reason: the conclusion of Lemma 3.3 with the key set replaced by {0,1}^{b+2}
--   - generalization: one implicit bit encoding of 𝔽_{2^b} → every bijection ι : GaloisField 2 b ≃ (Fin b → Bool); reason: the paper's encoding is one such ι
--   - encoding: branch bits of L, R, C and the fourth branch → 00, 01, 10 and 11; reason: the paper fixes no assignment
--   - encoding: Ext : {0,1}^{b+2} → {0,1} and U₁ the uniform law on {0,1}^1 → Ext : BitKey b → Bool (BitKey b = Fin (b+2) → Bool) and the uniform law on Bool; reason: {0,1}^1 and Bool are the same two-point set
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), proof of Theorem 1.1, §3.2, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_bitScheme

namespace SSNonExt

/-- **Lemma 3.3 on `{0,1}^{b+2}` (proof of Theorem 1.1).** "The set T in Lemma 3.3 depends only on the
restriction of the extractor to 𝒦, so the lemma applies verbatim to functions on {0, 1}^{b+2}": for every
`Ext : {0,1}^{b+2} → {0,1}` there is `T ⊆ V` such that `Ext` has statistical error at least `1/6` on
`P_T` or on `P_{T^c}`, the sources now read on bit strings.
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), proof of Theorem 1.1, §3.2, p.7 (PDF p.7).

**Formalization Note.** Keys are encoded by two branch bits followed by `ι i` for an arbitrary
bijection `ι : 𝔽_{2^b} ≃ {0,1}^b`; `bitP ι T` is the law of the encoded key under `P_T`. The
extractor may use all of `{0,1}^{b+2}`, including the fourth branch. -/
theorem lemma_3_3_bitstrings (b : ℕ) (hb : 2 ≤ b) (ι : V b ≃ (Fin b → Bool))
    (Ext : BitKey b → Bool) :
    ∃ T : Finset (V b),
      (1 / 6 : ℝ) ≤ TV ((bitP ι T).map Ext) (PMF.uniformOfFintype Bool) ∨
        (1 / 6 : ℝ) ≤ TV ((bitP ι Tᶜ).map Ext) (PMF.uniformOfFintype Bool) := by sorry

end SSNonExt
