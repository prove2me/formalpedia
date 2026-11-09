-- Prove2me | Theorems.Thm_QCSepTotal_proposition_2_4
-- name    : QCSepTotal.proposition_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:13.913251+00:00
-- url     : https://prove2.me/theorems/3ca45703-05fe-4c1e-88cd-2888e0bc3008
-- title:
--   Proposition 2.4 — certificate predicate $V_0$ with $b_0=O(S\log S)$, unique valid certificate, and a one-message affine-share test
-- statement:
--   There is an absolute constant $K_0$ with the following property. Let $D(z)$ be a Boolean predicate on $z\in\mathbb F_2^m$ computed by a circuit of size $S\ge2$. There are a certificate length $b_0$ with
--   $$1\le b_0\le K_0\,S\log S$$
--   and a predicate $V_0(z;p)$ on certificates $p\in\mathbb F_2^{b_0}$, where $p$ is called valid for $z$ when $V_0(z;p)=1$, such that
--
--   1. if $D(z)=1$, exactly one certificate is valid;
--   2. if $D(z)=0$, no certificate is valid;
--   3. given an additive sharing of $z$ and $p$ between two parties, there is a one-message randomized test with message length at most $K_0\log S$ bits. The message consists of a random challenge, independent of the input and the certificate, and four affine-answer shares; the receiver decides acceptance. The test accepts with probability $1$ when $p$ is valid for $z$, and with probability at most $1/64$ otherwise. It can be sent in either direction.
--
--   The paper quotes this from Gavinsky [10, Lemma 5.1], and footnote 3 justifies the uniqueness in property 1. In Section 3.1 it is applied to the circuit for $D_c$ to produce the certificates of $F_{\mathrm{tot}}$, and in Theorem 3.2 the test gives the extra quantum message.
--
--   **Formalization Note** The circuit reads coordinate $z_i\in\mathbb F_2$ as the bit $z_i=1$. The test is the affine-share test (challenge uniform in $\mathbb F_2^\ell$, four answer shares in $\mathbb F_2^w$, $\ell+4w$ bits); its condition is symmetric in the two shares.
--
--   Differences from the source:
--   - encoding: input z ∈ {0,1}^m read by the circuit → z ∈ (ZMod 2)^m, the circuit reading z_i = 1 as true; reason: the additive sharing is over F₂; same inputs
--   - encoding: one message of O(log S) bits with a random challenge and four affine-answer shares → a uniform challenge in F₂^ℓ and four F₂-affine answer shares in F₂^w, with ℓ + 4w ≤ K₀ log₂ S; reason: field elements of an extension of F₂ are bit vectors; this is the printed message structure
--   - encoding: the test can be sent in either direction → one test whose acceptance condition is symmetric in the two shares; reason: exchanging the roles gives the other direction
--   - reading: b₀ = O(S log S) and O(log S) bits → b₀ ≤ K₀ S log₂ S and ℓ + 4w ≤ K₀ log₂ S with one constant K₀ chosen before the circuit; reason: the meaning of O(·) uniform over all circuits
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Proposition 2.4, pp.5–6 (quoting [10, Lemma 5.1]); footnote 3, p.5

import Mathlib
import Definitions.Def_QCSepTotal_Circuit
import Definitions.Def_QCSepTotal_IsOneMsgTest

namespace QCSepTotal

/-- **Proposition 2.4** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), pp.5–6; quoting [10, Lemma 5.1], with the
uniqueness of footnote 3, p.5). Let `D(z)` be a Boolean predicate computed by a circuit of size
`S ≥ 2`. There is a predicate `V₀(z; p)` with certificates `p ∈ {0,1}^{b₀}` of positive length
`b₀ = O(S log S)` such that (1) if `D(z) = 1` exactly one certificate is valid; (2) if
`D(z) = 0` no certificate is valid; (3) given an additive sharing of `z` and `p` between two
parties, there is a one-message randomized test of `O(log S)` bits, containing a random challenge
independent of the input and certificate and four affine-answer shares, that accepts with
probability `1` when the certificate is valid and with probability at most `1/64` otherwise; the
receiver decides acceptance.

**Formalization Note.** The constant `K₀` of both `O(·)` bounds is chosen before the circuit.
Inputs are additively shared over `F₂ = ZMod 2`; the circuit reads `z i = 1` as `true`. The test
is `IsAffineShareTest` (challenge in `F₂^ℓ`, four answer shares in `F₂^w`, message of
`ℓ + 4w` bits); its condition is symmetric in the two shares, so it runs in either direction. -/
theorem proposition_2_4 :
    ∃ K₀ : ℝ, ∀ (m : ℕ) (C : Circuit (Fin m)), 2 ≤ C.size →
      ∃ b₀ : ℕ, 1 ≤ b₀ ∧ (b₀ : ℝ) ≤ K₀ * C.size * Real.logb 2 C.size ∧
        ∃ V₀ : (Fin m → ZMod 2) → (Fin b₀ → ZMod 2) → Bool,
          (∀ z, C.eval (fun i => decide (z i = 1)) = true → ∃! p, V₀ z p = true) ∧
          (∀ z, C.eval (fun i => decide (z i = 1)) = false → ∀ p, V₀ z p = false) ∧
          ∃ ℓ w : ℕ, ((ℓ + 4 * w : ℕ) : ℝ) ≤ K₀ * Real.logb 2 C.size ∧ IsAffineShareTest V₀ ℓ w := by sorry

end QCSepTotal
