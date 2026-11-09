-- Prove2me | Theorems.Thm_RandomQueryXOR_lemma_4_16
-- name    : RandomQueryXOR.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:13:58.638215+00:00
-- url     : https://prove2.me/theorems/453c2f97-91ff-449a-9fd1-c40111a896a2
-- title:
--   Lemma 4.16 — $I(\Pi';\theta\mid\rho,R^{\rm two}_{\rm pub},\alpha,\mathcal E_{\rm eq})\le \frac1{nd}\,\mathrm{IC}_{\mathcal D_{f\oplus}}(P)+S/d$
-- statement:
--   Let $P$ be a randomized gate-keeper branching program of width $2^S$ and length $T$ over $[2n]$, $x^\star$ an input with at least one sensitive zero, $d:=\mathrm{sens}_0[f,x^\star]\ge1$, and $k$ any number of players. The auxiliary transcript $\Pi'$ of $\pi_{\rm two}$ satisfies
--   $$
--   I\bigl(\Pi'\,;\,\theta\ \big|\ \rho,R^{\rm two}_{\rm pub},\alpha,\mathcal E_{\rm eq}\bigr)\ \le\ \frac1{nd}\,\mathrm{IC}_{\mathcal D_{f\oplus}}(P)+\frac Sd .
--   $$
--
--   This is the heart of the argument: the planted pair is one of $d$ indistinguishable pairs and each time step lands on it with probability $1/n$, so the information about the game revealed by the messages is a $1/(nd)$ fraction of the program's information cost, plus the final state.
--
--   Differences from the source:
--   - generalization: P the program of §4.2 solving g_{f⊕} with probability 2/3; x⋆_f from Assumption 4.2; k with k ≥ (4T log n)/n → any randomized gate-keeper program P, any x⋆ with a sensitive zero, any k; reason: the proof uses neither the correctness of P, nor the maximality of x⋆, nor the bound on k
--   - reading: the last player outputs P̂_k = P_{t̂_{k+1}} → the last block of Π′ ends at the state just before the (k+1)-th occurrence of h, P_{t̂_{k+1} − 1}; reason: the same sentence says the last block ends just before this occurrence
--   - encoding: π_two samples P̂_0 publicly conditioned on y and L; FAIL is declared → the gate bits before the first occurrence of h are public and P̂_0 is computed from them; on FAIL every player writes ⊥ and the answer is 0; reason: same joint law; given P̂_0 the transcript and θ are independent of those bits, and FAIL is a function of the public (h, M)
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Lemma 4.16, p.24 (PDF p.26); proof pp.25–28 (PDF pp.27–30); d := sens0[f, x⋆_f], p.22 (PDF p.24)

import Mathlib
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_gateSuccessProb
import Definitions.Def_RandomQueryXOR_infoCost
import Definitions.Def_RandomQueryXOR_hardDist
import Definitions.Def_RandomQueryXOR_TwoBitProtocol
import Definitions.Def_RandomQueryXOR_piTwo
import Definitions.Def_RandomQueryXOR_piAux

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

/-- Lemma 4.16 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.24 = PDF p.26): "The auxiliary transcript Π′ of π_two satisfies
I(Π′ ; θ | ρ, R^two_pub, α, E_eq) ≤ (1/(nd)) · IC_{D_{f⊕}}(P) + S/d", where "d := sens0[f, x⋆_f]".

**Formalization Note** `P` is any randomized gate-keeper program of width `2^S` and length `T`
over `[2n]` (its correctness is not used by the proof), `k` is arbitrary, and `x⋆ = xs` is any input
with at least one sensitive zero (so `d ≥ 1`). `IC` is `infoCost` with input distribution
`D_{f⊕} = hardDist f xs`. -/
theorem lemma_4_16 {n S T : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty) (μP : FinDist (DetBP (2 ^ S) (GateSample (Fin (2 * n))) T)) :
    cmi (condDist (piAux f xs k hZ μP).gameLaw Eeq) (piAux f xs k hZ μP).transcript theta
        (fun ω => (rho ω, pubR ω, alpha ω)) ≤
      1 / ((n : ℝ) * sens0At f xs) * infoCost μP (hardDist f xs) + S / (sens0At f xs : ℝ) := by sorry

end RandomQueryXOR
