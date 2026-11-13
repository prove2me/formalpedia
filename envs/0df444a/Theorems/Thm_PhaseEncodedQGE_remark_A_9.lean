-- Prove2me | Theorems.Thm_PhaseEncodedQGE_remark_A_9
-- name    : PhaseEncodedQGE.remark_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:58.129105+00:00
-- url     : https://prove2.me/theorems/7632f6fe-6404-45ce-98b2-d95f33a5e1ab
-- title:
--   Remark A.9 — the schedule constants $t^2=55.616$, $h_e-h_o=1.376,\,2.874$, gaps $0.1846,\,0.3854$
-- statement:
--   At the schedule $(\eta,\gamma)=(23/8,2)$, with $t=\tan(23/16)$:
--
--   1. $t^2=55.616$ (to three decimals);
--   2. hypothesis (a) of Theorem A.8, $t^2>n-m$, holds for every layer $m\ge1$ whenever $n\le56$;
--   3. $\min\{1,t^2-(n-m)\}=1$, so the gap is $|h_e-h_o|/t$, whenever $n-m\le54$;
--   4. $h_e-h_o=\cos3\gamma-\cos\gamma=1.376$ for $r=1$ and $(\cos3\gamma+\cos6\gamma)-(\cos\gamma+\cos2\gamma)=2.874$ for $r=2$ (to three decimals);
--   5. the gaps $|h_e-h_o|/t$ are $0.1846$ ($r=1$) and $0.3854$ ($r=2$) (to four decimals);
--   6. for $r=1$, $h_e\ne h_o$ if and only if $\gamma\notin(\pi/2)\mathbb Z$;
--   7. on a cubic graph every one-defect set $D=\{v\}$ has $E_{\mathrm{in}}=1$ and $E_{\mathrm{out}}=n-4$, so the one-defect layer has a single extremal profile.
--
--   These are the numbers behind the schedule clause of the goal; item 4 gives $h_e\ne h_o$ for PE-X2.
--
--   Differences from the source:
--   - encoding: printed decimals 55.616, 1.376, 2.874, 0.1846, 0.3854 → bounds $|v-d|<\tfrac12$ unit of the last printed digit; reason: a printed decimal is a rounded value
--   - encoding: 'the gap is $|h_e-h_o|/t$ whenever $n-m\le54$' → $\min\{1,t^2-(n-m)\}=1$ whenever $n-m\le54$; reason: the gap of Theorem A.8 is $|h_e-h_o|t^{-1}\min\{1,t^2-(n-m)\}$, which equals $|h_e-h_o|/t$ exactly when the minimum is 1
--   - reading: 'on a regular graph (E_in = 1, E_out = n − 4)' → for cubic graphs; reason: the profile is defined for k = 0..3 on cubic graphs and n − 4 = n − d − 1 only for d = 3
--   - reading: 'Hypothesis (b) gives determination for every n but no gap bound: … may shrink as n grows'; 'the first informative layer is m = 2' → not stated; reason: these sentences assert no theorem beyond Theorem A.8 (determination under (b)) and item 7
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.2, p.15 (PDF p.16), Remark A.9

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Remark A.9, the schedule constants (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.2, p.15).

At the schedule `t² = tan²(23/16) = 55.616`, so hypothesis (a) of Theorem A.8 holds for every layer
whenever `n ≤ 56` and the gap is `|h_e − h_o|/t` whenever `n − m ≤ 54`;
`h_e − h_o = cos 3γ − cos γ = 1.376` for `r = 1` and `(cos 3γ + cos 6γ) − (cos γ + cos 2γ) = 2.874`
for `r = 2`, so the gaps are `0.1846` and `0.3854`. For `r = 1` the condition `h_e ≠ h_o` is
`γ ∉ (π/2)ℤ`. The one-defect layer has a single profile on a regular graph (`E_in = 1`,
`E_out = n − 4`).

**Formalization Note** Each printed decimal is stated as a bound at its printed precision (half a
unit in the last printed digit). "Hypothesis (a) for every layer" is `n − m < t²` for every
`m ≥ 1`; "the gap is `|h_e − h_o|/t`" is `min{1, t² − (n − m)} = 1`. The gaps are
`|h_e − h_o|/t`. The one-defect clause is stated for cubic graphs, where `n − 4` is never truncated
(a cubic graph with a vertex has `n ≥ 4`). The sentence on hypothesis (b) ("the smallest difference
… may shrink as `n` grows") asserts no theorem and is not formalized. -/
theorem remark_A_9 :
    |Real.tan ((23 / 8 : ℝ) / 2) ^ 2 - 55.616| < 5e-4 ∧
    (∀ n m : ℕ, n ≤ 56 → 1 ≤ m → (n : ℝ) - m < Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
    (∀ n m : ℕ, (n : ℝ) - m ≤ 54 →
      min 1 (Real.tan ((23 / 8 : ℝ) / 2) ^ 2 - ((n : ℝ) - m)) = 1) ∧
    hX 1 2 0 - hX 1 2 1 = Real.cos (3 * 2) - Real.cos 2 ∧
    |(Real.cos (3 * 2) - Real.cos 2) - 1.376| < 5e-4 ∧
    hX 2 2 0 - hX 2 2 1 = (Real.cos (3 * 2) + Real.cos (6 * 2)) - (Real.cos 2 + Real.cos (2 * 2)) ∧
    |((Real.cos (3 * 2) + Real.cos (6 * 2)) - (Real.cos 2 + Real.cos (2 * 2))) - 2.874| < 5e-4 ∧
    |(|hX 1 2 0 - hX 1 2 1| / Real.tan ((23 / 8 : ℝ) / 2)) - 0.1846| < 5e-5 ∧
    |(|hX 2 2 0 - hX 2 2 1| / Real.tan ((23 / 8 : ℝ) / 2)) - 0.3854| < 5e-5 ∧
    (∀ γ : ℝ, hX 1 γ 0 ≠ hX 1 γ 1 ↔ ¬ ∃ k : ℤ, γ = Real.pi / 2 * k) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ v : Fin n,
      Ein G {v} = 1 ∧ Eout G {v} = n - 4) := by sorry

end PhaseEncodedQGE
