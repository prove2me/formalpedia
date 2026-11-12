-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_9
-- name    : SubcubicBA.PlainPKI.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:52.753631+00:00
-- url     : https://prove2.me/theorems/ca67fd06-92b5-4ca1-a8e4-d2d85cdb1848
-- title:
--   Theorem 9 — the bit recurrence solves to (κn)^p
-- statement:
--   Let $p=(\sqrt{13}-1)/2$. For all constants $K,C,C_0>0$ there are $B_0,c_0>0$ such that for all $B\ge B_0$ and $c\ge c_0$ there is $A>0$ with the following property. For every $\kappa\ge1$ and every function $f$ satisfying the bit recurrence of p. 32 with constant $C_0$ at the parameter rule $(m,b)=(n,1)$ for $n\le B\kappa^4$ and $m=b=\lceil c(\kappa n)^{p-1}\rceil$ otherwise (`BitRecurrence C₀ B c κ f`), and every $n\ge1$ with $\kappa\le K(\log_2 n)^C$,
--   $$f(n)\le A\,(\kappa n)^{p}.$$
--
--   Applied to the per-party bit complexity $B_{BA}$ of the protocol, this gives $B_{BA}(n)=O((\kappa n)^{(\sqrt{13}-1)/2})$, and with $n$ parties the total of Theorem 1.
--
--   Differences from the source:
--   - generalization: B_BA(n), the per-party bit complexity of the protocol → any nonnegative nondecreasing f with f(1) = 0 satisfying the displayed recurrence; reason: the recurrence holds for B_BA by Lemmas 21, 22, 24, 16, 19 and Theorems 5, 7; the theorem specializes to it
--   - reading: m = b = Θ((κn)^{(√13−3)/2}) ≈ Θ((κn)^{0.3077}) → m = b = ⌈c (κn)^{p−1}⌉ with p − 1 = (√13 − 3)/2 exactly; reason: the decimals 0.3077 and p ≈ 1.3077 are slips (paper.md item 6); the rule of p. 33 uses p − 1
--   - encoding: O(·) in the recurrence and in the conclusion; "for n large enough" → one constant C₀ for every n ≥ 2; ∃ B₀, c₀ ∀ B ≥ B₀, c ≥ c₀ ∃ A depending only on K, C, C₀, B, c; reason: the finitely many small n are absorbed into C₀ (the κnm term with m = n); the ∀ B ≥ B₀ shape lets one (B, c) serve Theorems 9 and 10
--   - encoding: κ = polylog(n) with κ ≤ K log^C n at the top level only (p. 32) → κ ≤ K (log₂ n)^C for the n of the conclusion; κ ≥ 1; reason: as in the proof; recursive calls need not satisfy it
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 9, p. 32 (recurrence after line 995, p. 32; parameter rule, p. 33)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Recurrences

namespace SubcubicBA.PlainPKI

/-- Theorem 9 (p. 32). -/
theorem theorem_9 (K C C₀ : ℝ) (hK : 0 < K) (hC : 0 < C) (hC₀ : 0 < C₀) :
    ∃ B₀ c₀ : ℝ, 0 < B₀ ∧ 0 < c₀ ∧ ∀ B c : ℝ, B₀ ≤ B → c₀ ≤ c → ∃ A : ℝ, 0 < A ∧
      ∀ (κ : ℕ) (f : ℕ → ℝ), 1 ≤ κ → BitRecurrence C₀ B c κ f →
        ∀ n : ℕ, 1 ≤ n → (κ : ℝ) ≤ K * Real.logb 2 n ^ C →
          f n ≤ A * ((κ : ℝ) * n) ^ pExp := by sorry

end SubcubicBA.PlainPKI
