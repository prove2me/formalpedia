-- Prove2me | Theorems.Thm_SensitivityCampaign_finite_certificate_rational
-- name    : SensitivityCampaign.finite_certificate_rational
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T03:04:12.023958+00:00
-- url     : https://prove2.me/theorems/ff43216d-099f-423f-8368-e09188f5867b
-- title:
--   Integer-power certificate for a rational sensitivity separation exponent
-- statement:
--   Let $p,q$ be natural numbers with $q>0$, and write $a=p/q$. Let $f:\{0,1\}^n\to\{0,1\}$ be a total Boolean function, let $x$ be any input, and let integers $A,B>1$ satisfy
--
--   $$
--   s(f)\le A,\qquad \mathrm{bs}(f,x)\ge B,\qquad A^p\le B^q.
--   $$
--
--   Then the exponent $a$ is achievable in the campaign's asymptotic sense: for every real $\varepsilon>0$ and every integer $S\ge2$, there are a dimension $m$ and a total Boolean function $g:\{0,1\}^m\to\{0,1\}$ such that
--
--   $$
--   s(g)\ge S,\qquad \mathrm{bs}(g)\ge s(g)^{a-\varepsilon}.
--   $$
--
--   This criterion allows a proposed rational exponent to be certified using an exact inequality between natural-number powers. In particular, the target exponent $2.10=21/10$ is certified by the integer inequality $A^{21}\le B^{10}$, together with the stated sensitivity bounds. The theorem is conditional on a finite function and its bounds; it does not supply a construction achieving that target.
-- source:
--   Original corollary of SensitivityCampaign.finite_certificate (Prove2Me shared campaign foundation), https://prove2.me/theorems/06deb432-c715-4a68-b79d-3078b3bc9a09. The integer-to-rational-power comparison uses Real.rpow_mul and Real.rpow_le_rpow_iff in Mathlib.Analysis.SpecialFunctions.Pow.Real. Campaign: https://prove2.me/campaigns/block-sensitivity-vs-sensitivity.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SensitivityCampaign
open OAI.Paper320

theorem SensitivityCampaign.finite_certificate_rational
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B p q : ℕ)
    (hA : 1 < A) (hB : 1 < B) (hq : 0 < q)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : A ^ p ≤ B ^ q) :
    SensitivityCampaign.AchievesExponent ((p : ℝ) / (q : ℝ)) := by sorry
