-- Prove2me | Theorems.Thm_RandOrderCSP_theorem_4_4
-- name    : RandOrderCSP.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:46.69901+00:00
-- url     : https://prove2.me/theorems/de5f115e-3dec-4b0d-975d-aeacd3a174c5
-- title:
--   Theorem 4.4 — linear lower bound for DIHP
-- statement:
--   For all $q,k\ge2$, every $k$-uniform $\Delta_1(\mathbb Z_q^k)$-colored gadget hypergraph $\Phi_*$, and every $\delta\in(0,1/2)$, there are $\alpha_0,c>0$ such that for all $\alpha\in(0,\alpha_0]$ and $T\ge1$ with $T\alpha^2\le c$, there are $n_0\in\mathbb N$ and $\tau\in(0,1)$ such that for every $n\ge n_0$, any deterministic protocol for $\mathrm{DIHP}_{\Phi_*}(\alpha,T,n)$ with advantage at least $\delta$ has communication cost at least $\tau n$ bits.
--
--   This is the communication lower bound from which the streaming lower bound is obtained by reduction.
--
--   Differences from the source:
--   - encoding: communication cost at least τn bits → every b bounding the total message length on all inputs has τn ≤ b; reason: the cost is the maximum of the total length; a protocol has cost ≥ τn iff every upper bound is ≥ τn
--   - encoding: each player is allowed to write H_t for free → every H_t is on the board; reason: a protocol may ignore the free entries; same class of protocols or stronger
--   - reading: a message of some number of bits → a bit string of any length (List Bool), the cost counting its length; reason: the page fixes no message format (its own reduction writes ⊥ or a state in {0,1}^s); fixed-width protocols are a special case, and a length-≤L message is recoverable from L+1 fixed bits, so the bound changes by at most T bits, absorbed in τ and n₀
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Theorem 4.4, p.17

import Mathlib
import Definitions.Def_RandOrderCSP_IsOneWiseUniform
import Definitions.Def_RandOrderCSP_DIHP

namespace RandOrderCSP

/-- **Theorem 4.4 (linear lower bound for DIHP).** Singer, Tulsiani, Velusamy, *A dichotomy theorem for
approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Theorem 4.4, p.17.

**Formalization Note.** "Communication cost at least `τn` bits" is: every `b` bounding the total message
length on all inputs satisfies `τn ≤ b`. `[Nonempty V]` is p.13's "All fixed base (gadget) hypergraphs
G∗ used below have nonempty vertex sets". -/
theorem theorem_4_4 {k q : ℕ} [NeZero q] (hk : 2 ≤ k) (hq : 2 ≤ q) {V E : Type} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype E] [DecidableEq E] (G : Hypergraph k V E)
    (Y : E → (Fin k → ZMod q) → ℝ) (hY : ∀ j, IsOneWiseUniform (Y j)) (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ < 1 / 2) :
    ∃ α₀ c : ℝ, 0 < α₀ ∧ 0 < c ∧
      ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ T : ℕ, 1 ≤ T → (T : ℝ) * α ^ 2 ≤ c →
        ∃ (n₀ : ℕ) (τ : ℝ), 0 < τ ∧ τ < 1 ∧
          ∀ n : ℕ, n₀ ≤ n → ∀ P : Protocol k q n E T,
            δ ≤ advantage G Y α n T P → ∀ b : ℕ, P.CostLE b → τ * (n : ℝ) ≤ b := by sorry

end RandOrderCSP
