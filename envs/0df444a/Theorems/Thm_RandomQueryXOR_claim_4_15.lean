-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_4_15
-- name    : RandomQueryXOR.claim_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:14:07.307733+00:00
-- url     : https://prove2.me/theorems/9ea6d54c-8166-4f62-839b-22adabe2c85c
-- title:
--   Claim 4.15 — removing FAIL costs at most $H_2(1/n^2)$
-- statement:
--   Let $P$ be a randomized gate-keeper branching program of width $2^S$ and length $T$ over $[2n]$, $x^\star$ an input with a sensitive zero, and
--   $$
--   k\ \ge\ \frac{4T\log_2 n}{n}.
--   $$
--   Let $\Pi^{\rm two}$ be the transcript of $\pi_{\rm two}$ and $\Pi'$ the auxiliary transcript, on the same probability space. Then
--   $$
--   I\bigl(\Pi^{\rm two}\,;\,\theta\ \big|\ \rho,R^{\rm two}_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr)\ \le\ H_2(1/n^2)+I\bigl(\Pi'\,;\,\theta\ \big|\ \rho,R^{\rm two}_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr),
--   $$
--   where $H_2(p)=-p\log_2p-(1-p)\log_2(1-p)$ is the binary entropy function.
--
--   The transcript of $\pi_{\rm two}$ is determined by $\Pi'$ and the indicator of FAIL, an event of probability at most $1/n^2$ by Claim 4.7, so FAIL changes the information by at most the entropy of that indicator.
--
--   Differences from the source:
--   - generalization: the standing assumption of §4.2 that P solves g_{f⊕} with probability of success at least 2/3; x⋆_f from Assumption 4.2 → any randomized gate-keeper program P and any x⋆ with a sensitive zero; reason: the proof uses neither the correctness of P nor the maximality of x⋆
--   - reading: the last player outputs P̂_k = P_{t̂_{k+1}} → the last block of Π′ ends at the state just before the (k+1)-th occurrence of h, P_{t̂_{k+1} − 1}; reason: the same sentence says the last block ends just before this occurrence
--   - encoding: π_two samples P̂_0 publicly conditioned on y and L; FAIL is declared → the gate bits before the first occurrence of h are public and P̂_0 is computed from them; on FAIL every player writes ⊥ and the answer is 0; reason: same joint law; given P̂_0 the transcript and θ are independent of those bits, and FAIL is a function of the public (h, M)
--   - encoding: log → Real.logb 2 (base 2); reason: the paper measures memory in bits; Real.logb 2 0 = 0 makes T = 0 harmless
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 4.15, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_gateSuccessProb
import Definitions.Def_RandomQueryXOR_TwoBitProtocol
import Definitions.Def_RandomQueryXOR_piTwo
import Definitions.Def_RandomQueryXOR_piAux

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

/-- Claim 4.15 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.24 = PDF p.26): "For the auxiliary transcript, we get,
I(Π^two ; θ | ρ, R^two_pub, α, E_eq) ≤ H_2(1/n²) + I(Π′ ; θ | ρ, R^two_pub, α, E_eq), where H_2() is the
binary entropy function", with the standing `k ≥ (4T log n)/n` of §4.2.

**Formalization Note** `Π^two` and `Π′` are the transcripts of `piTwo` and `piAux`, jointly
distributed on the same space (`piAux` has the same randomness as `piTwo`). `H_2` is the published
`WildeQIT.binaryEntropy`. The correctness of `P` (standing in §4.2) is not assumed: the proof does not
use it. -/
theorem claim_4_15 {n S T : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty) (μP : FinDist (DetBP (2 ^ S) (GateSample (Fin (2 * n))) T))
    (hk : 4 * (T : ℝ) * Real.logb 2 n / n ≤ k) :
    cmi (condDist (piTwo f xs k hZ μP).gameLaw Eeq) (piTwo f xs k hZ μP).transcript theta
        (fun ω => (rho ω, pubR ω, alpha ω)) ≤
      binaryEntropy (1 / (n : ℝ) ^ 2) +
        cmi (condDist (piTwo f xs k hZ μP).gameLaw Eeq) (piAux f xs k hZ μP).transcript theta
          (fun ω => (rho ω, pubR ω, alpha ω)) := by sorry

end RandomQueryXOR
