-- Prove2me | Theorems.Thm_SSNonExt_display_4
-- name    : SSNonExt.display_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:04:18.585219+00:00
-- url     : https://prove2.me/theorems/d1d9de1a-8630-4b3b-81a8-cf5373c9cd1c
-- title:
--   Proof of Lemma 3.3, display (4) — parity of $v_i$ and $\max\{|H_T|/Z_T,|H_{T^c}|/Z_{T^c}\}\ge 1/3$
-- statement:
--   Let $b\ge2$, $B=2^b$, $\mathrm{Ext}:\mathcal K\to\{0,1\}$, $h(k)=(-1)^{\mathrm{Ext}(k)}$, $H_T=\sum_{k\in\Omega_T}h(k)$, $Z_T=|\Omega_T|$, and
--
--   $$v_i=h(C_i)-h(L_i)-h(R_i)\qquad(i\in V).$$
--
--   Let $T=\{i:v_i>0\}$. Then:
--
--   1. every $v_i$ is odd, and $|v_i|\ge1$;
--   2. $T^c=\{i:v_i<0\}$; $v_i\in\{1,3\}$ for $i\in T$ and $v_i\in\{-1,-3\}$ for $i\in T^c$;
--   3. $H_T-H_{T^c}=\sum_{i\in T}v_i-\sum_{i\notin T}v_i=\sum_{i\in V}|v_i|\ge B$, and $Z_T+Z_{T^c}=3B$;
--   4. the chain
--
--   $$\max\Big\{\frac{|H_T|}{Z_T},\frac{|H_{T^c}|}{Z_{T^c}}\Big\}\ge\frac{|H_T|+|H_{T^c}|}{Z_T+Z_{T^c}}\ge\frac{H_T-H_{T^c}}{3B}\ge\frac13\tag{4}$$
--
--   holds.
--
--   Combined with the error identity this gives an error of at least $1/6$ on $P_T$ or $P_{T^c}$.
--
--   Differences from the source:
--   - encoding: Ext : 𝒦 → {0,1} and U₁ the uniform law on {0,1}^1 → Ext : Key b → Bool and the uniform law on Bool; reason: {0,1}^1 and Bool are the same two-point set
--   - encoding: the chain (4) → its three inequalities as separate conjuncts in ℝ, with the real max; reason: the same chain
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), proof of Lemma 3.3, display (4) and the two displays before it, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_SSNonExt_Hsum

namespace SSNonExt

/-- **Proof of Lemma 3.3, display (4).** With `v_i = h(C_i) − h(L_i) − h(R_i)`: each `v_i` is odd
and `|v_i| ≥ 1`; for `T = {i : v_i > 0}`, `T^c = {i : v_i < 0}`, `v_i ∈ {1, 3}` on `T` and
`v_i ∈ {−1, −3}` on `T^c`;
`H_T − H_{T^c} = ∑_{i∈T} v_i − ∑_{i∉T} v_i = ∑_{i∈V} |v_i| ≥ B`, `Z_T + Z_{T^c} = 3B`; and
`max{|H_T|/Z_T, |H_{T^c}|/Z_{T^c}} ≥ (|H_T| + |H_{T^c}|)/(Z_T + Z_{T^c}) ≥ (H_T − H_{T^c})/(3B) ≥ 1/3` (4).
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), proof of Lemma 3.3, display (4) and the two displays before it, p.7 (PDF p.7).

Standing hypothesis of §3: `b ≥ 2`; `B = 2^b`, `Z_T = |Ω_T|`.

**Formalization Note.** `T` is `posSet Ext = {i : v_i > 0}`, as on the page (not an arbitrary set).
The chain (4) is stated link by link in `ℝ`; the maximum is the real `max`. -/
theorem display_4 (b : ℕ) (hb : 2 ≤ b) (Ext : Key b → Bool) :
    (∀ i : V b, Odd (vDiff Ext i) ∧ 1 ≤ |vDiff Ext i|) ∧
      (posSet Ext)ᶜ = Finset.univ.filter (fun i => vDiff Ext i < 0) ∧
      (∀ i ∈ posSet Ext, vDiff Ext i = 1 ∨ vDiff Ext i = 3) ∧
      (∀ i ∈ (posSet Ext)ᶜ, vDiff Ext i = -1 ∨ vDiff Ext i = -3) ∧
      Hsum Ext (posSet Ext) - Hsum Ext (posSet Ext)ᶜ =
        ∑ i ∈ posSet Ext, vDiff Ext i - ∑ i ∈ (posSet Ext)ᶜ, vDiff Ext i ∧
      ∑ i ∈ posSet Ext, vDiff Ext i - ∑ i ∈ (posSet Ext)ᶜ, vDiff Ext i = ∑ i, |vDiff Ext i| ∧
      (2 : ℤ) ^ b ≤ ∑ i, |vDiff Ext i| ∧
      (Omega (posSet Ext)).card + (Omega (posSet Ext)ᶜ).card = 3 * 2 ^ b ∧
      (|(Hsum Ext (posSet Ext) : ℝ)| + |(Hsum Ext (posSet Ext)ᶜ : ℝ)|) /
          (((Omega (posSet Ext)).card : ℝ) + ((Omega (posSet Ext)ᶜ).card : ℝ)) ≤
        max (|(Hsum Ext (posSet Ext) : ℝ)| / ((Omega (posSet Ext)).card : ℝ))
          (|(Hsum Ext (posSet Ext)ᶜ : ℝ)| / ((Omega (posSet Ext)ᶜ).card : ℝ)) ∧
      ((Hsum Ext (posSet Ext) : ℝ) - (Hsum Ext (posSet Ext)ᶜ : ℝ)) / (3 * 2 ^ b) ≤
        (|(Hsum Ext (posSet Ext) : ℝ)| + |(Hsum Ext (posSet Ext)ᶜ : ℝ)|) /
          (((Omega (posSet Ext)).card : ℝ) + ((Omega (posSet Ext)ᶜ).card : ℝ)) ∧
      (1 / 3 : ℝ) ≤
        ((Hsum Ext (posSet Ext) : ℝ) - (Hsum Ext (posSet Ext)ᶜ : ℝ)) / (3 * 2 ^ b) := by sorry

end SSNonExt
