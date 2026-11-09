-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_4_12
-- name    : RandomQueryXOR.claim_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:11:44.492805+00:00
-- url     : https://prove2.me/theorems/a2c28d71-6819-4aab-afaf-c4812353739e
-- title:
--   Claim 4.12 — $\pi_{\rm two}$ succeeds with probability $\ge 2/3-1/n^2$
-- statement:
--   Let $P$ be a randomized branching program of length $T$ and width $2^S$ in the gate-keeper model that computes $g_{f\oplus}=f\circ\oplus_2$ with probability of success at least $2/3$ on every input $y\in\{0,1\}^{2n}$. Let $x^\star$ have at least one sensitive zero and let
--   $$
--   k\ \ge\ \frac{4T\log_2 n}{n}.
--   $$
--   Then the protocol $\pi_{\rm two}$ built from $P$ solves the two-bit parity game with $k$ players with probability of success at least
--   $$
--   \frac23-\frac1{n^2}.
--   $$
--
--   The protocol fails only when it declares FAIL (probability at most $1/n^2$ by Claim 4.7) or when $P$ errs on the planted input, whose value of $g$ is $f(x^\star)\oplus\alpha\oplus\beta$.
--
--   Differences from the source:
--   - generalization: x⋆_f a maximum-sensitivity input with sens0 ≥ sens1 (Assumption 4.2) → any x⋆ with at least one sensitive zero; reason: the proof uses only that h ranges over the nonempty set of sensitive zeros of x⋆
--   - encoding: π_two samples P̂_0 publicly conditioned on y and L; FAIL is declared → the gate bits before the first occurrence of h are public and P̂_0 is computed from them; on FAIL every player writes ⊥ and the answer is 0; reason: same joint law; given P̂_0 the transcript and θ are independent of those bits, and FAIL is a function of the public (h, M)
--   - encoding: log → Real.logb 2 (base 2); reason: the paper measures memory in bits; Real.logb 2 0 = 0 makes T = 0 harmless
--   - encoding: P a randomized branching program solving g_{f⊕} with probability of success at least 2/3 → a distribution on deterministic gate-keeper programs with gateSuccessProb ≥ 2/3 at every input; reason: π_two feeds P gate-keeper samples (ℓ_t, b_t, w); success is the minimum over inputs
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 4.12, p.22 (PDF p.24); standing assumptions §4.2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_xorLift
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_gateSuccessProb
import Definitions.Def_RandomQueryXOR_TwoBitProtocol
import Definitions.Def_RandomQueryXOR_piTwo

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Claim 4.12 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.22 = PDF p.24): "The probability of success of π_two is at least
2/3 − 1/n²", under the standing assumption of §4.2 (p.19 = PDF p.21: "we are given a randomized
branching program P that solves g_{f⊕} of length T and width 2^S with probability of success at
least 2/3") and `k ≥ (4T log n)/n`.

**Formalization Note** `P` is a randomized program in the gate-keeper model (π_two feeds it samples
`(ℓ_t, b_t, w)`) with success at least `2/3` on every input of `g = f ∘ ⊕2`. Success of π_two is
`Pr[answer = α ⊕ β]` under the law of the two-bit game. `x⋆ = xs` is any input with a sensitive
zero. -/
theorem claim_4_12 {n S T : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty) (μP : FinDist (DetBP (2 ^ S) (GateSample (Fin (2 * n))) T))
    (hP : ∀ y, (2 : ℝ) / 3 ≤ gateSuccessProb μP (xorLift f) y)
    (hk : 4 * (T : ℝ) * Real.logb 2 n / n ≤ k) :
    2 / 3 - 1 / (n : ℝ) ^ 2 ≤ (piTwo f xs k hZ μP).success := by sorry

end RandomQueryXOR
