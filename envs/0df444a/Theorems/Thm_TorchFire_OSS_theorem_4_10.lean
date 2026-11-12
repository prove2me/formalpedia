-- Prove2me | Theorems.Thm_TorchFire_OSS_theorem_4_10
-- name    : TorchFire.OSS.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:01.18398+00:00
-- url     : https://prove2.me/theorems/40c1f66f-4aa8-4d24-b2d2-838493a05bfa
-- title:
--   Theorem 4.10 — signing error $\epsilon_{y,b}$ (12) and correctness $\ge1-e(\lambda)$ of the repeated-trial signer
-- statement:
--   Let $\lambda\ge2$, fix the oracles of Construction 4.2 and $y\in\{0,1\}^r$, and let
--   $$\epsilon_{y,b}=\Pr\big[\mathrm{OSS.Ver}^O(y,b,u)=0:\ u\leftarrow\mathrm{OSS.Sign}^O(y,|W_y\rangle\langle W_y|,b)\big]$$
--   for the repeated-trial signer of Construction 4.7. With $e_1=(1,0,\dots,0)\in\mathbb Z_2^k$,
--   $$\epsilon_{y,b}=\begin{cases}2^{-\lambda},&e_1^{\mathsf T}A_y\ne0^{n-r},\\1[(b_y)_1\ne b],&e_1^{\mathsf T}A_y=0^{n-r}.\end{cases}\quad(12)$$
--   In particular Construction 4.7 is correct with probability at least $1-e(\lambda)$, $e(\lambda)=2^{-\lambda}+2^{-(n-r)}$: for each message bit $b$, sampling the oracles, generating a key with $\mathrm{OSS.GenQKey}$, signing $b$ and verifying succeeds with probability at least $1-e(\lambda)$.
--
--   The theorem is adapted from [ÇGS26, Theorem 11]; the source states it for its Construction 4.7 and gives no proof. It supplies the signing errors $e_A,e_T$ of torch-fire's correctness proof.
--
--   Differences from the source:
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - reading: "Construction 4.7 satisfies correctness with probability at least 1 − e(λ)" → for each message bit b, the probability of correctness (2) is at least 1 − e(λ); reason: Definition 4.1 (2) for the message space {0,1}
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Theorem 4.10, (12), p.22 (adapted from [ÇGS26, Theorem 11])

import Mathlib
import Definitions.Def_TorchFire_OSS_longForgeProb

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

/-- **Theorem 4.10** (Construction 4.7 correctness, adapted from [ÇGS26, Theorem 11]), p.22 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593).
For `λ ≥ 2`, fixed oracles and `y ∈ {0,1}^r`, the signing error `ϵ_{y,b}` of the repeated-trial signer
on `|W_y⟩⟨W_y|` is `2^{−λ}` if `e_1ᵀ A_y ≠ 0^{n−r}` and `1[(b_y)_1 ≠ b]` if `e_1ᵀ A_y = 0^{n−r}` (12); and
Construction 4.7 is correct with probability at least `1 − e(λ)`, `e(λ) = 2^{−λ} + 2^{−(n−r)}`, for each
message bit `b`. The source cites [ÇGS26] and gives no proof. -/
theorem theorem_4_10 (lam : ℕ) (hlam : 2 ≤ lam) :
    (∀ (ω : OneSample lam) (y : Bits (r lam)) (b : ZMod 2),
      signErr ω y b =
        if Matrix.vecMul (Pi.single (⟨0, k_pos lam⟩ : Fin (k lam)) (1 : ZMod 2)) (Amat ω y) ≠ 0
        then (2 : ℝ)⁻¹ ^ lam
        else if firstBit (bvec ω y) ≠ b then 1 else 0) ∧
    ∀ b : ZMod 2, 1 - ((2 : ℝ)⁻¹ ^ lam + (2 : ℝ)⁻¹ ^ nr lam) ≤ oneCorrProb lam b := by sorry

end TorchFire.OSS
