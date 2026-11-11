-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_2_2
-- name    : QuantumAdviceAmplification.Separation.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:36.666501+00:00
-- url     : https://prove2.me/theorems/d10799b9-fef3-43cd-9aae-555cc19eee02
-- title:
--   Lemma 2.2 — Stability
-- statement:
--   Let $0\le\varepsilon\le\widehat\varepsilon\le1/2$, $\eta,\theta\ge0$, $H(\widehat\varepsilon)-H(\varepsilon)\le\theta$, and $a\ge1$. Then
--   $$\min\{1/2,\widehat\varepsilon+a\Phi(\widehat\varepsilon,\eta)\}\le\min\{1/2,\varepsilon+(2a+1)\Phi(\varepsilon,\eta+\theta)\}.$$
--   This gives a uniform way to absorb nearby error parameters and their entropy losses.
--
--   Differences from the source: none.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.5, Lemma 2.2

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_2_2 (ε εhat η θ a : ℝ) (hε : 0 ≤ ε) (horder : ε ≤ εhat)
    (hhat : εhat ≤ 1 / 2) (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hH : H εhat - H ε ≤ θ) (ha : 1 ≤ a) :
    min (1 / 2) (εhat + a * Φ εhat η) ≤
      min (1 / 2) (ε + (2 * a + 1) * Φ ε (η + θ)) := by sorry

end QuantumAdviceAmplification.Separation
