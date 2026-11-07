-- Prove2me | Theorems.Thm_RevisitXor_bounded_variances_W
-- name    : RevisitXor.bounded_variances_W
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:23.041035+00:00
-- url     : https://prove2.me/theorems/ef98f3ad-36b8-4624-ad80-ad0a94f6e1f4
-- title:
--   Method of bounded variances for $W$: $\mathbb P[W\ge\mathbb E W+t]\le2\exp(-t^2/(c\sum v_i+cbt))$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $M=2^m$ and $h:[2]^{2m}\to[2]$. Let $b\ge0$ and $v_1,\dots,v_{M/2}$ be numbers with $|W_i-\mathbb E[W_i]|\le b$ and $\operatorname{var}W_i\le v_i$ for every $i$, every outcome $x_{<i}$ and every value of $X_i$. Then for every $t\ge0$
--
--   $$\mathbb P_\Pi\big[W\ge\mathbb E[W]+t\big]\le2\exp\!\Big(-\frac{t^2}{c\sum_{i\le M/2}v_i+cbt}\Big).$$
--
--   With Lemma 6 ($b\le c$, $v_i\le c/(M-2(i-1))$, so $\sum v_i\le c\log M$) this gives exponential decay in $t$ for $t\ge c\log M$, which is Claim (1). The method is Freedman's inequality for the Doob martingale of $W$ along the edge sequence.
--
--   **Formalization Note** The probability and $\mathbb E[W]$ are over the uniform law on valid edge sequences. When the denominator is $0$, $W$ is constant and the bound reads $2$.
--
--   Differences from the source:
--   - generalization: b and v_i as given by Lemma 6 (|W_i − E[W_i]| := b, var W_i := v_i) → any b and v_i bounding |W_i − E[W_i]| and var W_i for every outcome and next edge; reason: the method needs bounds that do not depend on the outcome; the maxima over outcomes are an instance, so the statement specializes to the printed one
--   - reading: t unrestricted in the display → t ≥ 0; reason: the method's range; the paper applies it with t ≥ c log M; for t < 0 the display is false in general (when W is constant, b = 0 and every v_i = 1 are admissible bounds; for t < 0 the left side is 1 while the right side 2·exp(−2t²/(cM)) is below 1 once t² > cM·log 2/2)
--   - encoding: the two occurrences of c → one constant c > 0; reason: p.1 convention; one constant is the special case c₁ = c₂ and implies the two-constant form
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.7

import Mathlib
import Definitions.Def_RevisitXor_Wi

namespace RevisitXor

/-- **The method of bounded variances for `W`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), §1, p.7: "The method of bounded variances then says the following.
P_Π[W ≥ E[W] + t] ≤ 2 · exp(−t² / (c Σ_{i≤M/2} vi + cbt))."

For every `b` bounding `|W_i − E[W_i]|` and every `v_i` bounding `var W_i`, over all outcomes
`x_{<i}` and next edges, the upper tail of `W` satisfies the display.

**Formalization Note.** `b` and `v_i` are any deterministic bounds valid for every outcome (the
method requires such bounds; the paper's `b` and `v_i` of Lemma 6 are instances, e.g. the maxima).
One absolute `c > 0` serves both occurrences. The probability and `E[W]` are over the uniform law on
valid edge sequences, written as a ratio of cardinalities and `avg`. The display is claimed for
`t ≥ 0`, the range of the method; for `t < 0` it is false in general. -/
theorem bounded_variances_W :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, ∀ h : Cube m × Cube m → ZMod 2, ∀ (b : ℝ) (v : ℕ → ℝ),
      (∀ ys ∈ validSeqs m, ∀ i : ℕ, 1 ≤ i → i ≤ 2 ^ m / 2 →
        ∀ e ∈ pairsIn (remaining ys i), |Wi h ys i e - EWi h ys i| ≤ b) →
      (∀ ys ∈ validSeqs m, ∀ i : ℕ, 1 ≤ i → i ≤ 2 ^ m / 2 → varWi h ys i ≤ v i) →
      ∀ t : ℝ, 0 ≤ t →
        (((validSeqs m).filter fun xs => avg (validSeqs m) (W h) + t ≤ W h xs).card : ℝ) /
            (validSeqs m).card ≤
          2 * Real.exp (-t ^ 2 / (c * ∑ i ∈ Finset.Icc 1 (2 ^ m / 2), v i + c * b * t)) := by sorry

end RevisitXor
