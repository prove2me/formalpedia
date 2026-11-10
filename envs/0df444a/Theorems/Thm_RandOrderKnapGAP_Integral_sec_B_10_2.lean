-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_sec_B_10_2
-- name    : RandOrderKnapGAP.Integral.sec_B_10_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:43.126558+00:00
-- url     : https://prove2.me/theorems/c63cb812-9c3a-4336-89c3-98a75b3d0a40
-- title:
--   §B.10.2 — inserting dummies online yields a uniformly random permutation of all real and dummy identities
-- statement:
--   Let $n$ real requests arrive in a uniformly random order $\sigma$, and insert $d$ labeled dummy requests online: when $r'$ real and $d'$ dummy requests remain unplaced, place the next real arrival with probability $r'/(r'+d')$, and otherwise a uniformly chosen remaining dummy. Then every remaining identity is equally likely to appear next, and by induction the resulting sequence is a uniformly random permutation of all $N=n+d$ real and dummy identities:
--   $$\frac1{n!}\sum_{\sigma}\Pr(\text{output}=\tau\mid\sigma)=\frac1{(n+d)!}\qquad\text{for every arrangement }\tau .$$
--   In particular, the relative order of the real requests is unchanged: every arrangement produced from $\sigma$ lists the real requests in the order $\sigma$.
--
--   Differences from the source:
--   - encoding: the online insertion procedure and its output sequence of the N real and dummy identities → insertionProb σ τ (product of the step probabilities) for τ : Fin (n + d) ≃ Fin n ⊕ Fin d; N = n + d; reason: the law of the procedure's output given σ; averaging over the uniform σ gives the law of the output
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), pp. 63–64 (PDF 65–66), §B.10.2

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_DummyInsertion

open scoped BigOperators

namespace RandOrderKnapGAP.Integral

/-- **§B.10.2** (dummy insertion), pp. 63–64. Let the `n` real requests arrive in a uniformly
random order `σ` and insert `d` labeled dummies online by the rule of §B.10.2. Then the
resulting augmented sequence is a uniformly random arrangement of all `n + d` real and dummy
identities: every `τ` has probability `1/(n+d)!`. Moreover, on every outcome of the procedure
the relative order of the real requests is unchanged. -/
theorem sec_B_10_2 (n d : ℕ) :
    (∀ τ : Fin (n + d) ≃ Fin n ⊕ Fin d,
      (∑ σ : Equiv.Perm (Fin n), insertionProb σ τ) / (Nat.factorial n : ℝ)
        = 1 / (Nat.factorial (n + d) : ℝ)) ∧
    (∀ (σ : Equiv.Perm (Fin n)) (τ : Fin (n + d) ≃ Fin n ⊕ Fin d), insertionProb σ τ ≠ 0 →
      ∀ j j' : Fin n, (σ.symm j < σ.symm j' ↔ τ.symm (Sum.inl j) < τ.symm (Sum.inl j'))) := by sorry

end RandOrderKnapGAP.Integral
