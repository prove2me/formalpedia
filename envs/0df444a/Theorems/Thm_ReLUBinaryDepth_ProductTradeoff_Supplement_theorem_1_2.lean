-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_Supplement_theorem_1_2
-- name    : ReLUBinaryDepth.ProductTradeoff.Supplement.theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T12:45:36.476323+00:00
-- url     : https://prove2.me/theorems/59223862-bf33-4c14-91ac-a6dd54b1219c
-- title:
--   Theorem 1.2 — TC⁰ approximation of the bounded Boolean product
-- statement:
--   There are an absolute depth bound $d$ and an absolute constant $c$ with the following property. Let $K\ge 0$ and $N\ge 1$ be integers, let $n\ge 0$, and let $\theta_i(0),\theta_i(1)\in[0,2^K]$ be arbitrary real constants for $i=1,\dots,n$. Then there is a threshold circuit $\Phi$ with $n$ inputs and $R$ output bits, together with a number $F$ of fractional bits, such that
--
--   1. $\Phi$ has depth at most $d$;
--   2. $\Phi$ has size (gates plus wires) at most $c\,(n+N+K+1)^c$, and $R\le c\,(n+N+K+1)^c$;
--   3. for every $x\in\{0,1\}^n$, the nonnegative dyadic rational $\widehat P(x)=\mathrm{val}_F(\Phi(x))$ satisfies
--   $$\Bigl|\widehat P(x)-\prod_{i=1}^n\theta_i(x_i)\Bigr|\le 2^{-N}.$$
--
--   Here gates are threshold gates over possibly negated, repeatable literals with integer thresholds (polynomially bounded integer weights), the standard $\mathrm{TC}^0$ basis. The circuit may depend on $K$, $n$, $N$ and the constants $\theta$; no uniformity is claimed.
--
--   The theorem shows that the exact-computation lower bound of Theorem 1.1 depends on infinite accuracy: the product family is approximated to $N$ bits by constant-depth polynomial-size threshold circuits.
--
--   Differences from the source:
--   - reading: a TC0 circuit of size polynomial in n, N, and K → one absolute depth bound d and one polynomial c·(n+N+K+1)^c, both fixed before K, n, N and θ; the circuit itself may depend on all of them; reason: this is what membership of a family in TC0 means; a per-instance depth or polynomial would make the claim vacuous
--   - reading: TC0 circuit (Section 3 allows real-weighted threshold gates) → the published QNatProofs.ThrCircuit: integer thresholds over negatable, repeatable literals (polynomially bounded integer weights), size = gates + wires; reason: the narrowest standard TC0 basis and the largest size measure give the strongest existence claim; it implies the statement for real-weighted gates
--   - reading: size polynomial in n, N, K → additionally the number R of output bits is at most the same polynomial; reason: output literals are not counted in ThrCircuit.size; bounding them keeps the whole circuit, outputs included, polynomial, as the source intends
--   - encoding: outputs a nonnegative dyadic rational P̂(x) → R output bits read in binary fixed point with F fractional bits, (Σ_r b_r 2^r)/2^F; reason: standard binary encoding of nonnegative dyadic rationals; every such value is a nonnegative dyadic rational and conversely
--   - encoding: θ_i for i = 1, …, n; x ∈ {0,1}^n → θ : Fin n → Bool → ℝ, x : Fin n → Bool, product via the published productMap; reason: zero-based indices and Booleans for bits; same instances (n = 0 gives the empty product 1)
-- source:
--   Neil Krishnan, Elchanan Mossel, Depth Lower Bounds for ReLU Networks with Binary Inputs, STOC 2027 submission #1645 (October 2026), Theorem 1.2, PDF p. 3 = printed p. 3; proof sketch p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf (SHA-256 35accc05b120367e3d7a527b3b55383bc4a42c205bc78904f41eea6b2668555b)

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Product
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Dyadic
import Definitions.Def_QNatProofs_ThrCircuit

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff

/-- Theorem 1.2, PDF = printed p. 3. One absolute depth bound `d` and one polynomial `c·(n+N+K+1)^c`
are fixed before every instance; the circuit may depend on `K, n, N, θ`. -/
theorem theorem_1_2 :
    ∃ d c : ℕ, ∀ (K n N : ℕ), 1 ≤ N → ∀ θ : Fin n → Bool → ℝ,
      (∀ i b, 0 ≤ θ i b ∧ θ i b ≤ (2 : ℝ) ^ K) →
      ∃ (R F : ℕ) (Φ : QNatProofs.ThrCircuit n R),
        Φ.depth ≤ d ∧ Φ.size ≤ c * (n + N + K + 1) ^ c ∧ R ≤ c * (n + N + K + 1) ^ c ∧
        ∀ x : Cube n, |dyadicValue F (Φ.eval x) - productMap θ x| ≤ (2 : ℝ) ^ (-(N : ℤ)) := by sorry

end ReLUBinaryDepth.ProductTradeoff.Supplement
