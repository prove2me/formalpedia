-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_B_2
-- name    : UCalibDirichlet.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:57.770196+00:00
-- url     : https://prove2.me/theorems/2fec4aee-44d0-4170-b0b8-0e8e8d20849c
-- title:
--   Lemma B.2 — Bernstein error of the binary entropy $\ge 1/(12T)$
-- statement:
--   Let $h(x)=-x\log x-(1-x)\log(1-x)$ be the binary entropy, with $h(0)=h(1)=0$. For every integer $T\ge2$,
--   $$\min_{x\in\mathcal G_T\setminus\{0,1\}}\big\{h(x)-(B_Th)(x)\big\}\ge\frac1{12T},$$
--   where $\mathcal G_T=\{0,1/T,\dots,1\}$; that is, $h(k/T)-(B_Th)(k/T)\ge 1/(12T)$ for $k=1,\dots,T-1$.
--
--   This shows that the binary entropy is an admissible regularizer in Lemma B.1 with $\gamma\ge 1/(12T)$.
--
--   Differences from the source:
--   - encoding: min over x ∈ G_T ∖ {0,1} → ∀ k : ℕ, 1 ≤ k → k < T → bound at x = k/T; reason: a minimum over a finite set is at least a bound iff every element is
--   - encoding: h the binary entropy (natural log) → Real.binEntropy; reason: same function, including h(0) = h(1) = 0
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma B.2, display (45), p.29

import Mathlib
import Definitions.Def_UCalibDirichlet_bern

namespace UCalibDirichlet

/-- **Lemma B.2 (Bernstein error of the binary entropy).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Lemma B.2, display (45), p.29: "Let
`h(x) := −x log x − (1 − x) log(1 − x)` denote the binary entropy (with `h(0) = h(1) = 0`). Then
for every integer `T ≥ 2`, `min_{x∈G_T∖{0,1}} { h(x) − (B_T h)(x) } ≥ 1/(12T)`. (45)"

Here `G_T = {0, 1/T, …, 1}` (Lemma B.1), so `G_T ∖ {0,1} = {k/T : 1 ≤ k ≤ T − 1}`, and the minimum
is at least `1/(12T)` exactly when every grid value is.

**Formalization Note.** `h` is Mathlib's `Real.binEntropy` (natural logarithm,
`binEntropy 0 = binEntropy 1 = 0`), which is the paper's `h`. `B_T` is `bern`. -/
theorem lemma_B_2 (T : ℕ) (hT : 2 ≤ T) (k : ℕ) (hk1 : 1 ≤ k) (hkT : k < T) :
    1 / (12 * (T : ℝ)) ≤ Real.binEntropy (k / T) - bern Real.binEntropy T (k / T) := by sorry

end UCalibDirichlet
