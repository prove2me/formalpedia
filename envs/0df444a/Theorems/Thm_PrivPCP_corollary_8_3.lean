-- Prove2me | Theorems.Thm_PrivPCP_corollary_8_3
-- name    : PrivPCP.corollary_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:48.381593+00:00
-- url     : https://prove2.me/theorems/20592c3a-54db-42bb-ad7e-aa1f472cfc43
-- title:
--   Corollary 8.3 (with Theorem 1.2): private PCPs for Circuit-SAT
-- statement:
--   There is an absolute constant $C>0$ such that:
--
--   1. **(Corollary 8.3)** for every $k\ge2$ and every $\rho\in(0,1]$ at which the product-expansion property of Conjecture 4.2 holds with $\eta=1/128$, $\beta=4$ at every arity $2\le r\le k$, Circuit-SAT has a private PCP in which
--      - the honest proof $\Pi(\Phi,w)$ is polynomial-time samplable for every circuit $\Phi$ and every assignment $w$;
--      - the verifier is a nonadaptive probabilistic polynomial-time machine making at most $C\,k\,M^{1/k}$ queries;
--      - on instances of size $n\ge1$ the proof has size $M\le n\log(n+1)\,e^{Ck\log k}$ over an alphabet of prime size $q\le M^6$;
--      - completeness is perfect and the soundness error is at most $1-e^{-Ck}$;
--      - the PCP is $\nu$-private with
--   $$\nu(n)=\frac{1}{\log(n+1)}\exp\!\big(-C(k^3+k^2\log(1/\rho))\big);$$
--   2. **(Theorem 1.2, $k=2$)** for $k=2$ such a private PCP exists unconditionally, for some $\rho_2\in(0,1]$.
--
--   Privacy means that for every circuit, every two assignments $w,w'$ (satisfying or not) and every set $T$ of proof positions of verifier-induced measure below $\nu$, the honest proofs of $w$ and $w'$ have the same law on $T$. For $k=2$ this gives $\sqrt M$-query private PCPs with privacy $\Omega(1/\log n)$; for growing $k$ it gives almost-linear-size private PCPs, the classical analogue of the witness encoding in the Anshu–Breuckmann–Nguyen approach to quantum PCPs.
--
--   **Formalization Note** The $O(\cdot)$ are one constant $C$, fixed before $k$, $\rho$ and $n$; the paper's $\nu_k$ is replaced by its "In particular" lower bound, and $\nu$-privacy is monotone in $\nu$.
--
--   Differences from the source:
--   - generalization: assume Conjecture 4.2 and put $\rho=\rho(k,1/128,4)$ → any $\rho\in(0,1]$ with $\mathrm{PunctRSPE}(r,1/128,4,\rho)$ for every $2\le r\le k$; reason: the proof uses product expansion at arities $2..k$ only (Corollary 4.3's proof, p.14); under Conjecture 4.2 with $\rho(\cdot)$ nonincreasing in $r$, $\rho(k,1/128,4)$ satisfies the hypothesis
--   - reading: a CircuitSAT instance of size $n$ has a private PCP of size $M$ over $\mathbb F_q$ → one prover sampler and one verifier for all circuits, with $M$, $q$ functions of $n$; reason: Definition 8.2's prover and verifier act on every circuit; Lemma 5.4 chooses the parameters from $n$ and $k$
--   - reading: Boolean circuit of size $n$ → fan-in-two circuits over the full binary basis with free constants; size = inputs + gates; reason: the paper fixes no basis; this contains $\{\wedge,\vee,\neg\}$ circuits, and other size conventions change $n$ by a constant factor absorbed by $C$
--   - reading: Theorem 1.2: for $k=2$ unconditionally, for $n>k$ → conjunct (b): $k=2$ with some $\rho_2\in(0,1]$, bounds for every $n\ge1$; reason: the unconditional case uses Theorem 4.11's constant; all $n\ge1$ includes $n>2$
--   - encoding: $M\le n\log(n+1)e^{O(k\log k)}$, $O(kM^{1/k})$ queries, error $1-e^{-O(k)}$, $\nu_k\ge e^{-O(k^3+k^2\log(1/\rho))}/\log(n+1)$ → the same bounds with one absolute $C$; reason: the standard meaning of $O(\cdot)$; $\nu_k$-privacy implies privacy at any smaller threshold
--   - encoding: alphabet $\mathbb F_q$ → $\Sigma=\{0,\dots,q-1\}$ with $q$ prime; reason: only the size and the primality of the alphabet enter the statement
--   - encoding: $\mu_{V,\Phi}$: verifier coins, then a uniform queried coordinate → $2^{-\rho_V}\sum_r|T\cap Q(r)|/|Q(r)|$, a coin string with $Q(r)=\emptyset$ contributing $0$, $Q(r)$ read against a reference proof $\pi_0$ quantified universally; reason: the paper's verifier always queries; nonadaptivity makes $Q(r)$ independent of the proof
--   - encoding: perfect completeness $\Pr_{\pi,V}[V^\pi(\Phi)=1]=1$ → acceptance for every proof in the support and every coin string; reason: a finite probability space; same condition
--   - encoding: polynomial-time samplable prover, PPT verifier → oracle Turing machines with polynomially bounded coin lengths and clocks; the sampler outputs the code of a proof whose law is exactly $\Pi(\Phi,w)$; reason: the standard machine reading
--   - reading: $\Pi(\Phi,w)$ is a polynomial-time samplable distribution → the sampler draws $\sigma$ uniform bits and $\sigma$ uniform elements of $\Sigma=\mathbb F_q$; reason: the paper's honest prover samples uniform polynomials and certificates over $\mathbb F_q$ (§5.2, p.28; §6.2, p.36) and privacy is an exact equality of laws, which no fixed number of bit coins achieves for odd $q$; a field-coin sampler is an exact Las Vegas bit sampler in expected polynomial time, so this is the standard notion and not a weaker one
--   - encoding: $\rho$-product-expanding → `GoodQLTC.IsProductExpanding`, which includes $\rho>0$; reason: every use has $\rho\in(0,1]$
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Corollary 8.3, p.46 (PDF p.48); Theorem 1.2, p.2 (PDF p.4); Definition 8.2, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_PrivPCP_HasPrivatePCP
import Definitions.Def_PrivPCP_PunctRSPE

namespace PrivPCP

/-- **Corollary 8.3 (Private PCP)**, with **Theorem 1.2**'s unconditional case `k = 2` (Bafna, Vyas, *Private PCPs
from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Corollary 8.3, p.46, and Theorem 1.2,
p.2). There is an absolute constant `C > 0` such that:

(a) for every `k ⩾ 2` and every `ρ ∈ (0,1]` at which the product expansion of Conjecture 4.2 holds for
`η = 1/128`, `β = 4` and every arity `2 ⩽ r ⩽ k`, Circuit-SAT has a private PCP with a polynomial-time prover
sampler, a nonadaptive PPT verifier making at most `C k M^{1/k}` queries, size
`M ⩽ n log(n+1) e^{C k log k}`, a prime alphabet `q ⩽ M⁶`, perfect completeness, soundness error at most
`1 − e^{−Ck}`, and privacy `e^{−C(k³ + k² log(1/ρ))}/log(n+1)`;

(b) for `k = 2` this holds unconditionally, for some `ρ₂ ∈ (0,1]`.

**Formalization Note** The `O(·)` are one absolute `C`, fixed before `k`, `ρ` and `n`. The paper's `ν_k` is
bounded below by its "In particular" form, and `ν`-privacy is monotone in `ν`. The paper assumes Conjecture 4.2
and puts `ρ = ρ(k, 1/128, 4)`, with `ρ(·, η, β)` nonincreasing in the arity; this gives product expansion with
constant `ρ` at every arity `2 ⩽ r ⩽ k`, the hypothesis of (a). One system serves all circuits; `M`, `q` are
functions of the circuit size `n` (inputs plus gates), with the bounds required for `n ⩾ 1`. -/
theorem corollary_8_3 : ∃ C : ℝ, 0 < C ∧
    (∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (∀ r : ℕ, 2 ≤ r → r ≤ k → PunctRSPE r (1 / 128) 4 ρ) → HasPrivatePCP C k ρ) ∧
    (∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ρ₂ ≤ 1 ∧ HasPrivatePCP C 2 ρ₂) := by sorry

end PrivPCP
